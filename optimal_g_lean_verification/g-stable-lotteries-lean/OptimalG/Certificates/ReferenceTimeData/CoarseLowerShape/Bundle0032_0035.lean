import OptimalG.Certificates.ReferenceSupportGeometry
import OptimalG.Certificates.ReferenceMatchedFrame
import OptimalG.Certificates.ReferenceBranchGeometry
import OptimalG.Certificates.ReferenceTimeBounds
import OptimalG.Certificates.ReferenceFrozenProfiles
import OptimalG.Certificates.ReferenceHessianFrame
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0029_0032
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0029_0032
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0065_0068
import OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Bundle0030_0033
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0031_0034
import OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Bundle0028_0031
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0033_0036
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0033_0036
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0069_0072
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Bundle0034_0037
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0035_0038

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0032
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch64_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0064.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0064.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch65_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0065.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0065.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile256_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.r256=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0032.r256.bounds := by rfl
theorem a_profile256_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.a256=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0032.a256.bounds := by rfl
theorem r_fixed256_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.r256.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r256.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r256.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r256.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed 7 := by decide +kernel
theorem a_fixed256_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.a256.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.a256.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed 9 := by decide +kernel
theorem ranks256_linked : ReferenceRankData.CoarseLowerShape.Batch0032.targetR256=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0032.targetA256=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed 1 := by decide +kernel
theorem r_input256_linked : ReferenceRankData.CoarseLowerShape.Batch0032.r256.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0032.r256.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0032.r256.bounds.gauge] := by decide +kernel
theorem a_input256_linked : ReferenceRankData.CoarseLowerShape.Batch0032.a256.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0032.a256.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0032.a256.bounds.gauge] := by decide +kernel
theorem geometry256_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.right.a := by decide +kernel
theorem weights512_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0064.cert512.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights513_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0064.cert513.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time256_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed 10)=true := by decide +kernel
theorem r_reference256_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed 0)=true := by decide +kernel
theorem a_reference256_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed 1)=true := by decide +kernel
theorem rank_r_link256_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0032.r256.bounds ReferenceRankData.CoarseLowerShape.Batch0032.r256 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link256_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0032.a256.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a256 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints256 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell true ReferenceProfileData.CoarseLowerShape.Batch0032.r256.bounds ReferenceRankData.CoarseLowerShape.Batch0032.r256 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile256_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0032.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0032.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link256_checked
    geometry256_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell false ReferenceProfileData.CoarseLowerShape.Batch0032.a256.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a256 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile256_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0032.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0032.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link256_checked
    geometry256_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks256_linked.1,←ranks256_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0032.r256.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a256.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0032.ordered256_checked hr ha ho
theorem frozen_frame256 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256 ReferenceProfileData.CoarseLowerShape.Batch0032.r256.bounds ReferenceProfileData.CoarseLowerShape.Batch0032.a256.bounds
  · rw [←r_profile256_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile256_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry256_linked.2.2.2.2.1
  · exact geometry256_linked.2.2.2.2.2
  · exact r_reference256_checked
  · exact a_reference256_checked
  · exact r_fixed256_linked
  · exact a_fixed256_linked
  · exact time256_checked
  · exact ht
  · exact hw
theorem child_geometry256_checked : ReferenceWeightData.CoarseLowerShape.Batch0064.cert512.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0064.cert512.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0064.cert513.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0064.cert513.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights256 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0064.cert512∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch64_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0064.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0064.cert513∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch64_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0064.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0064.cert512.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0064.cert512.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0064.cert512.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry256_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights512_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0064.cert513.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0064.cert513.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry256_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry256_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights513_linked j (List.mem_finRange j))
theorem actual_frozen_frame256 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame256 (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.flow.timeParameter_mem child_geometry256_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights256 hz)
theorem r_profile257_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.r257=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0032.r257.bounds := by rfl
theorem a_profile257_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.a257=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0032.a257.bounds := by rfl
theorem r_fixed257_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.r257.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r257.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r257.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r257.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed 7 := by decide +kernel
theorem a_fixed257_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.a257.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.a257.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed 9 := by decide +kernel
theorem ranks257_linked : ReferenceRankData.CoarseLowerShape.Batch0032.targetR257=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0032.targetA257=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed 1 := by decide +kernel
theorem r_input257_linked : ReferenceRankData.CoarseLowerShape.Batch0032.r257.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0032.r257.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0032.r257.bounds.gauge] := by decide +kernel
theorem a_input257_linked : ReferenceRankData.CoarseLowerShape.Batch0032.a257.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0032.a257.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0032.a257.bounds.gauge] := by decide +kernel
theorem geometry257_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.right.a := by decide +kernel
theorem weights514_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0064.cert514.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights515_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0064.cert515.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time257_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed 10)=true := by decide +kernel
theorem r_reference257_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed 0)=true := by decide +kernel
theorem a_reference257_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed 1)=true := by decide +kernel
theorem rank_r_link257_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0032.r257.bounds ReferenceRankData.CoarseLowerShape.Batch0032.r257 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link257_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0032.a257.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a257 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints257 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell true ReferenceProfileData.CoarseLowerShape.Batch0032.r257.bounds ReferenceRankData.CoarseLowerShape.Batch0032.r257 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile257_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0032.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0032.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link257_checked
    geometry257_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell false ReferenceProfileData.CoarseLowerShape.Batch0032.a257.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a257 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile257_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0032.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0032.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link257_checked
    geometry257_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks257_linked.1,←ranks257_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0032.r257.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a257.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0032.ordered257_checked hr ha ho
theorem frozen_frame257 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257 ReferenceProfileData.CoarseLowerShape.Batch0032.r257.bounds ReferenceProfileData.CoarseLowerShape.Batch0032.a257.bounds
  · rw [←r_profile257_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile257_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry257_linked.2.2.2.2.1
  · exact geometry257_linked.2.2.2.2.2
  · exact r_reference257_checked
  · exact a_reference257_checked
  · exact r_fixed257_linked
  · exact a_fixed257_linked
  · exact time257_checked
  · exact ht
  · exact hw
theorem child_geometry257_checked : ReferenceWeightData.CoarseLowerShape.Batch0064.cert514.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0064.cert514.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0064.cert515.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0064.cert515.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights257 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0064.cert514∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch64_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0064.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0064.cert515∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch64_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0064.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0064.cert514.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0064.cert514.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0064.cert514.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry257_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights514_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0064.cert515.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0064.cert515.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry257_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry257_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights515_linked j (List.mem_finRange j))
theorem actual_frozen_frame257 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame257 (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.flow.timeParameter_mem child_geometry257_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights257 hz)
theorem r_profile258_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.r258=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0032.r258.bounds := by rfl
theorem a_profile258_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.a258=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0032.a258.bounds := by rfl
theorem r_fixed258_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.r258.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r258.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r258.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r258.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed 7 := by decide +kernel
theorem a_fixed258_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.a258.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.a258.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed 9 := by decide +kernel
theorem ranks258_linked : ReferenceRankData.CoarseLowerShape.Batch0032.targetR258=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0032.targetA258=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed 1 := by decide +kernel
theorem r_input258_linked : ReferenceRankData.CoarseLowerShape.Batch0032.r258.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0032.r258.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0032.r258.bounds.gauge] := by decide +kernel
theorem a_input258_linked : ReferenceRankData.CoarseLowerShape.Batch0032.a258.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0032.a258.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0032.a258.bounds.gauge] := by decide +kernel
theorem geometry258_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.right.a := by decide +kernel
theorem weights516_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0064.cert516.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights517_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0064.cert517.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time258_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed 10)=true := by decide +kernel
theorem r_reference258_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed 0)=true := by decide +kernel
theorem a_reference258_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed 1)=true := by decide +kernel
theorem rank_r_link258_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0032.r258.bounds ReferenceRankData.CoarseLowerShape.Batch0032.r258 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link258_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0032.a258.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a258 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints258 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell true ReferenceProfileData.CoarseLowerShape.Batch0032.r258.bounds ReferenceRankData.CoarseLowerShape.Batch0032.r258 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile258_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0032.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0032.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link258_checked
    geometry258_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell false ReferenceProfileData.CoarseLowerShape.Batch0032.a258.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a258 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile258_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0032.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0032.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link258_checked
    geometry258_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks258_linked.1,←ranks258_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0032.r258.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a258.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0032.ordered258_checked hr ha ho
theorem frozen_frame258 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258 ReferenceProfileData.CoarseLowerShape.Batch0032.r258.bounds ReferenceProfileData.CoarseLowerShape.Batch0032.a258.bounds
  · rw [←r_profile258_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile258_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry258_linked.2.2.2.2.1
  · exact geometry258_linked.2.2.2.2.2
  · exact r_reference258_checked
  · exact a_reference258_checked
  · exact r_fixed258_linked
  · exact a_fixed258_linked
  · exact time258_checked
  · exact ht
  · exact hw
theorem child_geometry258_checked : ReferenceWeightData.CoarseLowerShape.Batch0064.cert516.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0064.cert516.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0064.cert517.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0064.cert517.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights258 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0064.cert516∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch64_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0064.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0064.cert517∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch64_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0064.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0064.cert516.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0064.cert516.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0064.cert516.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry258_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights516_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0064.cert517.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0064.cert517.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry258_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry258_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights517_linked j (List.mem_finRange j))
theorem actual_frozen_frame258 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame258 (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.flow.timeParameter_mem child_geometry258_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights258 hz)
theorem r_profile259_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.r259=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0032.r259.bounds := by rfl
theorem a_profile259_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.a259=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0032.a259.bounds := by rfl
theorem r_fixed259_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.r259.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r259.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r259.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r259.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed 7 := by decide +kernel
theorem a_fixed259_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.a259.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.a259.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed 9 := by decide +kernel
theorem ranks259_linked : ReferenceRankData.CoarseLowerShape.Batch0032.targetR259=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0032.targetA259=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed 1 := by decide +kernel
theorem r_input259_linked : ReferenceRankData.CoarseLowerShape.Batch0032.r259.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0032.r259.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0032.r259.bounds.gauge] := by decide +kernel
theorem a_input259_linked : ReferenceRankData.CoarseLowerShape.Batch0032.a259.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0032.a259.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0032.a259.bounds.gauge] := by decide +kernel
theorem geometry259_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.right.a := by decide +kernel
theorem weights518_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0064.cert518.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights519_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0064.cert519.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time259_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed 10)=true := by decide +kernel
theorem r_reference259_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed 0)=true := by decide +kernel
theorem a_reference259_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed 1)=true := by decide +kernel
theorem rank_r_link259_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0032.r259.bounds ReferenceRankData.CoarseLowerShape.Batch0032.r259 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link259_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0032.a259.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a259 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints259 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell true ReferenceProfileData.CoarseLowerShape.Batch0032.r259.bounds ReferenceRankData.CoarseLowerShape.Batch0032.r259 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile259_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0032.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0032.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link259_checked
    geometry259_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell false ReferenceProfileData.CoarseLowerShape.Batch0032.a259.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a259 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile259_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0032.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0032.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link259_checked
    geometry259_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks259_linked.1,←ranks259_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0032.r259.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a259.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0032.ordered259_checked hr ha ho
theorem frozen_frame259 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259 ReferenceProfileData.CoarseLowerShape.Batch0032.r259.bounds ReferenceProfileData.CoarseLowerShape.Batch0032.a259.bounds
  · rw [←r_profile259_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile259_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry259_linked.2.2.2.2.1
  · exact geometry259_linked.2.2.2.2.2
  · exact r_reference259_checked
  · exact a_reference259_checked
  · exact r_fixed259_linked
  · exact a_fixed259_linked
  · exact time259_checked
  · exact ht
  · exact hw
theorem child_geometry259_checked : ReferenceWeightData.CoarseLowerShape.Batch0064.cert518.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0064.cert518.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0064.cert519.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0064.cert519.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights259 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0064.cert518∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch64_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0064.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0064.cert519∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch64_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0064.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0064.cert518.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0064.cert518.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0064.cert518.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry259_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights518_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0064.cert519.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0064.cert519.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry259_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry259_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights519_linked j (List.mem_finRange j))
theorem actual_frozen_frame259 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame259 (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.flow.timeParameter_mem child_geometry259_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights259 hz)
theorem r_profile260_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.r260=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0032.r260.bounds := by rfl
theorem a_profile260_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.a260=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0032.a260.bounds := by rfl
theorem r_fixed260_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.r260.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r260.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r260.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r260.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed 7 := by decide +kernel
theorem a_fixed260_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.a260.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.a260.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed 9 := by decide +kernel
theorem ranks260_linked : ReferenceRankData.CoarseLowerShape.Batch0032.targetR260=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0032.targetA260=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed 1 := by decide +kernel
theorem r_input260_linked : ReferenceRankData.CoarseLowerShape.Batch0032.r260.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0032.r260.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0032.r260.bounds.gauge] := by decide +kernel
theorem a_input260_linked : ReferenceRankData.CoarseLowerShape.Batch0032.a260.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0032.a260.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0032.a260.bounds.gauge] := by decide +kernel
theorem geometry260_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.right.a := by decide +kernel
theorem weights520_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0065.cert520.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights521_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0065.cert521.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time260_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed 10)=true := by decide +kernel
theorem r_reference260_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed 0)=true := by decide +kernel
theorem a_reference260_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed 1)=true := by decide +kernel
theorem rank_r_link260_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0032.r260.bounds ReferenceRankData.CoarseLowerShape.Batch0032.r260 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link260_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0032.a260.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a260 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints260 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell true ReferenceProfileData.CoarseLowerShape.Batch0032.r260.bounds ReferenceRankData.CoarseLowerShape.Batch0032.r260 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile260_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0032.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0032.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link260_checked
    geometry260_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell false ReferenceProfileData.CoarseLowerShape.Batch0032.a260.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a260 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile260_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0032.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0032.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link260_checked
    geometry260_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks260_linked.1,←ranks260_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0032.r260.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a260.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0032.ordered260_checked hr ha ho
theorem frozen_frame260 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260 ReferenceProfileData.CoarseLowerShape.Batch0032.r260.bounds ReferenceProfileData.CoarseLowerShape.Batch0032.a260.bounds
  · rw [←r_profile260_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile260_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry260_linked.2.2.2.2.1
  · exact geometry260_linked.2.2.2.2.2
  · exact r_reference260_checked
  · exact a_reference260_checked
  · exact r_fixed260_linked
  · exact a_fixed260_linked
  · exact time260_checked
  · exact ht
  · exact hw
theorem child_geometry260_checked : ReferenceWeightData.CoarseLowerShape.Batch0065.cert520.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0065.cert520.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0065.cert521.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0065.cert521.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights260 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0065.cert520∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch65_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0065.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0065.cert521∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch65_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0065.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0065.cert520.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0065.cert520.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0065.cert520.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry260_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights520_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0065.cert521.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0065.cert521.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry260_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry260_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights521_linked j (List.mem_finRange j))
theorem actual_frozen_frame260 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame260 (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.flow.timeParameter_mem child_geometry260_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights260 hz)
theorem r_profile261_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.r261=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0032.r261.bounds := by rfl
theorem a_profile261_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.a261=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0032.a261.bounds := by rfl
theorem r_fixed261_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.r261.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r261.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r261.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r261.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed 7 := by decide +kernel
theorem a_fixed261_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.a261.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.a261.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed 9 := by decide +kernel
theorem ranks261_linked : ReferenceRankData.CoarseLowerShape.Batch0032.targetR261=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0032.targetA261=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed 1 := by decide +kernel
theorem r_input261_linked : ReferenceRankData.CoarseLowerShape.Batch0032.r261.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0032.r261.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0032.r261.bounds.gauge] := by decide +kernel
theorem a_input261_linked : ReferenceRankData.CoarseLowerShape.Batch0032.a261.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0032.a261.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0032.a261.bounds.gauge] := by decide +kernel
theorem geometry261_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.right.a := by decide +kernel
theorem weights522_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0065.cert522.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights523_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0065.cert523.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time261_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed 10)=true := by decide +kernel
theorem r_reference261_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed 0)=true := by decide +kernel
theorem a_reference261_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed 1)=true := by decide +kernel
theorem rank_r_link261_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0032.r261.bounds ReferenceRankData.CoarseLowerShape.Batch0032.r261 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link261_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0032.a261.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a261 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints261 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell true ReferenceProfileData.CoarseLowerShape.Batch0032.r261.bounds ReferenceRankData.CoarseLowerShape.Batch0032.r261 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile261_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0032.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0032.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link261_checked
    geometry261_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell false ReferenceProfileData.CoarseLowerShape.Batch0032.a261.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a261 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile261_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0032.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0032.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link261_checked
    geometry261_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks261_linked.1,←ranks261_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0032.r261.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a261.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0032.ordered261_checked hr ha ho
theorem frozen_frame261 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261 ReferenceProfileData.CoarseLowerShape.Batch0032.r261.bounds ReferenceProfileData.CoarseLowerShape.Batch0032.a261.bounds
  · rw [←r_profile261_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile261_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry261_linked.2.2.2.2.1
  · exact geometry261_linked.2.2.2.2.2
  · exact r_reference261_checked
  · exact a_reference261_checked
  · exact r_fixed261_linked
  · exact a_fixed261_linked
  · exact time261_checked
  · exact ht
  · exact hw
theorem child_geometry261_checked : ReferenceWeightData.CoarseLowerShape.Batch0065.cert522.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0065.cert522.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0065.cert523.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0065.cert523.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights261 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0065.cert522∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch65_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0065.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0065.cert523∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch65_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0065.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0065.cert522.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0065.cert522.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0065.cert522.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry261_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights522_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0065.cert523.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0065.cert523.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry261_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry261_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights523_linked j (List.mem_finRange j))
theorem actual_frozen_frame261 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame261 (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.flow.timeParameter_mem child_geometry261_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights261 hz)
theorem r_profile262_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.r262=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0032.r262.bounds := by rfl
theorem a_profile262_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.a262=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0032.a262.bounds := by rfl
theorem r_fixed262_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.r262.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r262.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r262.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r262.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed 7 := by decide +kernel
theorem a_fixed262_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.a262.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.a262.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed 9 := by decide +kernel
theorem ranks262_linked : ReferenceRankData.CoarseLowerShape.Batch0032.targetR262=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0032.targetA262=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed 1 := by decide +kernel
theorem r_input262_linked : ReferenceRankData.CoarseLowerShape.Batch0032.r262.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0032.r262.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0032.r262.bounds.gauge] := by decide +kernel
theorem a_input262_linked : ReferenceRankData.CoarseLowerShape.Batch0032.a262.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0032.a262.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0032.a262.bounds.gauge] := by decide +kernel
theorem geometry262_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.right.a := by decide +kernel
theorem weights524_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0065.cert524.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights525_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0065.cert525.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time262_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed 10)=true := by decide +kernel
theorem r_reference262_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed 0)=true := by decide +kernel
theorem a_reference262_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed 1)=true := by decide +kernel
theorem rank_r_link262_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0032.r262.bounds ReferenceRankData.CoarseLowerShape.Batch0032.r262 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link262_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0032.a262.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a262 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints262 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell true ReferenceProfileData.CoarseLowerShape.Batch0032.r262.bounds ReferenceRankData.CoarseLowerShape.Batch0032.r262 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile262_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0032.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0032.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link262_checked
    geometry262_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell false ReferenceProfileData.CoarseLowerShape.Batch0032.a262.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a262 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile262_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0032.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0032.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link262_checked
    geometry262_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks262_linked.1,←ranks262_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0032.r262.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a262.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0032.ordered262_checked hr ha ho
theorem frozen_frame262 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262 ReferenceProfileData.CoarseLowerShape.Batch0032.r262.bounds ReferenceProfileData.CoarseLowerShape.Batch0032.a262.bounds
  · rw [←r_profile262_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile262_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry262_linked.2.2.2.2.1
  · exact geometry262_linked.2.2.2.2.2
  · exact r_reference262_checked
  · exact a_reference262_checked
  · exact r_fixed262_linked
  · exact a_fixed262_linked
  · exact time262_checked
  · exact ht
  · exact hw
theorem child_geometry262_checked : ReferenceWeightData.CoarseLowerShape.Batch0065.cert524.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0065.cert524.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0065.cert525.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0065.cert525.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights262 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0065.cert524∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch65_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0065.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0065.cert525∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch65_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0065.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0065.cert524.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0065.cert524.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0065.cert524.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry262_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights524_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0065.cert525.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0065.cert525.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry262_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry262_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights525_linked j (List.mem_finRange j))
theorem actual_frozen_frame262 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame262 (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.flow.timeParameter_mem child_geometry262_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights262 hz)
theorem r_profile263_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.r263=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0032.r263.bounds := by rfl
theorem a_profile263_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.a263=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0032.a263.bounds := by rfl
theorem r_fixed263_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.r263.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r263.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r263.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.r263.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed 7 := by decide +kernel
theorem a_fixed263_linked : ReferenceProfileData.CoarseLowerShape.Batch0032.a263.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0032.a263.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed 9 := by decide +kernel
theorem ranks263_linked : ReferenceRankData.CoarseLowerShape.Batch0032.targetR263=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0032.targetA263=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed 1 := by decide +kernel
theorem r_input263_linked : ReferenceRankData.CoarseLowerShape.Batch0032.r263.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0032.r263.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0032.r263.bounds.gauge] := by decide +kernel
theorem a_input263_linked : ReferenceRankData.CoarseLowerShape.Batch0032.a263.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0032.a263.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0032.a263.bounds.gauge] := by decide +kernel
theorem geometry263_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.right.a := by decide +kernel
theorem weights526_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0065.cert526.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights527_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0065.cert527.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time263_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed 10)=true := by decide +kernel
theorem r_reference263_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed 0)=true := by decide +kernel
theorem a_reference263_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed 1)=true := by decide +kernel
theorem rank_r_link263_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0032.r263.bounds ReferenceRankData.CoarseLowerShape.Batch0032.r263 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link263_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0032.a263.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a263 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints263 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell true ReferenceProfileData.CoarseLowerShape.Batch0032.r263.bounds ReferenceRankData.CoarseLowerShape.Batch0032.r263 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile263_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0032.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0032.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link263_checked
    geometry263_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell false ReferenceProfileData.CoarseLowerShape.Batch0032.a263.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a263 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile263_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0032.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0032.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link263_checked
    geometry263_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks263_linked.1,←ranks263_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0032.r263.bounds ReferenceRankData.CoarseLowerShape.Batch0032.a263.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0032.ordered263_checked hr ha ho
theorem frozen_frame263 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263 ReferenceProfileData.CoarseLowerShape.Batch0032.r263.bounds ReferenceProfileData.CoarseLowerShape.Batch0032.a263.bounds
  · rw [←r_profile263_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile263_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry263_linked.2.2.2.2.1
  · exact geometry263_linked.2.2.2.2.2
  · exact r_reference263_checked
  · exact a_reference263_checked
  · exact r_fixed263_linked
  · exact a_fixed263_linked
  · exact time263_checked
  · exact ht
  · exact hw
theorem child_geometry263_checked : ReferenceWeightData.CoarseLowerShape.Batch0065.cert526.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0065.cert526.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0065.cert527.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0065.cert527.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights263 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0065.cert526∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch65_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0065.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0065.cert527∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch65_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0065.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0065.cert526.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0065.cert526.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0065.cert526.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry263_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights526_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0065.cert527.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0065.cert527.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry263_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry263_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights527_linked j (List.mem_finRange j))
theorem actual_frozen_frame263 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame263 (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.flow.timeParameter_mem child_geometry263_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights263 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell256),(ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell257),(ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell258),(ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell259),(ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell260),(ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell261),(ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell262),(ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0032.cell263)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0032.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0032.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame256 hz
  · exact fun z hz=>actual_frozen_frame257 hz
  · exact fun z hz=>actual_frozen_frame258 hz
  · exact fun z hz=>actual_frozen_frame259 hz
  · exact fun z hz=>actual_frozen_frame260 hz
  · exact fun z hz=>actual_frozen_frame261 hz
  · exact fun z hz=>actual_frozen_frame262 hz
  · exact fun z hz=>actual_frozen_frame263 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints256 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints257 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints258 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints259 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints260 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints261 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints262 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints263 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry256_linked.1,geometry256_linked.2.1,geometry256_linked.2.2.1,geometry256_linked.2.2.2.1⟩
  · exact ⟨geometry257_linked.1,geometry257_linked.2.1,geometry257_linked.2.2.1,geometry257_linked.2.2.2.1⟩
  · exact ⟨geometry258_linked.1,geometry258_linked.2.1,geometry258_linked.2.2.1,geometry258_linked.2.2.2.1⟩
  · exact ⟨geometry259_linked.1,geometry259_linked.2.1,geometry259_linked.2.2.1,geometry259_linked.2.2.2.1⟩
  · exact ⟨geometry260_linked.1,geometry260_linked.2.1,geometry260_linked.2.2.1,geometry260_linked.2.2.2.1⟩
  · exact ⟨geometry261_linked.1,geometry261_linked.2.1,geometry261_linked.2.2.1,geometry261_linked.2.2.2.1⟩
  · exact ⟨geometry262_linked.1,geometry262_linked.2.1,geometry262_linked.2.2.1,geometry262_linked.2.2.2.1⟩
  · exact ⟨geometry263_linked.1,geometry263_linked.2.1,geometry263_linked.2.2.1,geometry263_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0032.a256.bounds,?_,geometry256_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0032.a256.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile256_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0032.r256.bounds,?_,geometry256_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert256.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0032.r256.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile256_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0032.a257.bounds,?_,geometry257_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0032.a257.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile257_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0032.r257.bounds,?_,geometry257_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert257.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0032.r257.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile257_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0032.a258.bounds,?_,geometry258_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0032.a258.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile258_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0032.r258.bounds,?_,geometry258_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert258.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0032.r258.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile258_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0032.a259.bounds,?_,geometry259_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0032.a259.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile259_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0032.r259.bounds,?_,geometry259_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert259.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0032.r259.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile259_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0032.a260.bounds,?_,geometry260_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0032.a260.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile260_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0032.r260.bounds,?_,geometry260_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert260.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0032.r260.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile260_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0032.a261.bounds,?_,geometry261_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0032.a261.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile261_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0032.r261.bounds,?_,geometry261_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert261.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0032.r261.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile261_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0032.a262.bounds,?_,geometry262_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0032.a262.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile262_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0032.r262.bounds,?_,geometry262_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert262.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0032.r262.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile262_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0032.a263.bounds,?_,geometry263_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0032.a263.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile263_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0032.r263.bounds,?_,geometry263_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0032.cert263.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0032.r263.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile263_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0032.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0032.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0032

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0033
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch66_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0066.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0066.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch67_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0067.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0067.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile264_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.r264=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0033.r264.bounds := by rfl
theorem a_profile264_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.a264=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0033.a264.bounds := by rfl
theorem r_fixed264_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.r264.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r264.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r264.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r264.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed 7 := by decide +kernel
theorem a_fixed264_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.a264.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.a264.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed 9 := by decide +kernel
theorem ranks264_linked : ReferenceRankData.CoarseLowerShape.Batch0033.targetR264=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0033.targetA264=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed 1 := by decide +kernel
theorem r_input264_linked : ReferenceRankData.CoarseLowerShape.Batch0033.r264.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0033.r264.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0033.r264.bounds.gauge] := by decide +kernel
theorem a_input264_linked : ReferenceRankData.CoarseLowerShape.Batch0033.a264.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0033.a264.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0033.a264.bounds.gauge] := by decide +kernel
theorem geometry264_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.right.a := by decide +kernel
theorem weights528_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0066.cert528.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights529_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0066.cert529.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time264_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed 10)=true := by decide +kernel
theorem r_reference264_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed 0)=true := by decide +kernel
theorem a_reference264_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed 1)=true := by decide +kernel
theorem rank_r_link264_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0033.r264.bounds ReferenceRankData.CoarseLowerShape.Batch0033.r264 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link264_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0033.a264.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a264 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints264 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell true ReferenceProfileData.CoarseLowerShape.Batch0033.r264.bounds ReferenceRankData.CoarseLowerShape.Batch0033.r264 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile264_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0033.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0033.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link264_checked
    geometry264_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell false ReferenceProfileData.CoarseLowerShape.Batch0033.a264.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a264 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile264_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0033.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0033.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link264_checked
    geometry264_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks264_linked.1,←ranks264_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0033.r264.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a264.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0033.ordered264_checked hr ha ho
theorem frozen_frame264 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264 ReferenceProfileData.CoarseLowerShape.Batch0033.r264.bounds ReferenceProfileData.CoarseLowerShape.Batch0033.a264.bounds
  · rw [←r_profile264_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile264_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry264_linked.2.2.2.2.1
  · exact geometry264_linked.2.2.2.2.2
  · exact r_reference264_checked
  · exact a_reference264_checked
  · exact r_fixed264_linked
  · exact a_fixed264_linked
  · exact time264_checked
  · exact ht
  · exact hw
theorem child_geometry264_checked : ReferenceWeightData.CoarseLowerShape.Batch0066.cert528.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0066.cert528.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0066.cert529.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0066.cert529.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights264 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0066.cert528∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch66_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0066.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0066.cert529∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch66_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0066.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0066.cert528.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0066.cert528.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0066.cert528.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry264_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights528_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0066.cert529.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0066.cert529.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry264_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry264_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights529_linked j (List.mem_finRange j))
theorem actual_frozen_frame264 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame264 (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.flow.timeParameter_mem child_geometry264_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights264 hz)
theorem r_profile265_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.r265=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0033.r265.bounds := by rfl
theorem a_profile265_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.a265=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0033.a265.bounds := by rfl
theorem r_fixed265_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.r265.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r265.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r265.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r265.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed 7 := by decide +kernel
theorem a_fixed265_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.a265.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.a265.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed 9 := by decide +kernel
theorem ranks265_linked : ReferenceRankData.CoarseLowerShape.Batch0033.targetR265=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0033.targetA265=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed 1 := by decide +kernel
theorem r_input265_linked : ReferenceRankData.CoarseLowerShape.Batch0033.r265.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0033.r265.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0033.r265.bounds.gauge] := by decide +kernel
theorem a_input265_linked : ReferenceRankData.CoarseLowerShape.Batch0033.a265.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0033.a265.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0033.a265.bounds.gauge] := by decide +kernel
theorem geometry265_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.right.a := by decide +kernel
theorem weights530_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0066.cert530.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights531_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0066.cert531.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time265_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed 10)=true := by decide +kernel
theorem r_reference265_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed 0)=true := by decide +kernel
theorem a_reference265_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed 1)=true := by decide +kernel
theorem rank_r_link265_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0033.r265.bounds ReferenceRankData.CoarseLowerShape.Batch0033.r265 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link265_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0033.a265.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a265 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints265 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell true ReferenceProfileData.CoarseLowerShape.Batch0033.r265.bounds ReferenceRankData.CoarseLowerShape.Batch0033.r265 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile265_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0033.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0033.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link265_checked
    geometry265_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell false ReferenceProfileData.CoarseLowerShape.Batch0033.a265.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a265 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile265_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0033.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0033.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link265_checked
    geometry265_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks265_linked.1,←ranks265_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0033.r265.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a265.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0033.ordered265_checked hr ha ho
theorem frozen_frame265 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265 ReferenceProfileData.CoarseLowerShape.Batch0033.r265.bounds ReferenceProfileData.CoarseLowerShape.Batch0033.a265.bounds
  · rw [←r_profile265_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile265_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry265_linked.2.2.2.2.1
  · exact geometry265_linked.2.2.2.2.2
  · exact r_reference265_checked
  · exact a_reference265_checked
  · exact r_fixed265_linked
  · exact a_fixed265_linked
  · exact time265_checked
  · exact ht
  · exact hw
theorem child_geometry265_checked : ReferenceWeightData.CoarseLowerShape.Batch0066.cert530.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0066.cert530.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0066.cert531.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0066.cert531.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights265 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0066.cert530∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch66_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0066.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0066.cert531∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch66_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0066.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0066.cert530.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0066.cert530.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0066.cert530.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry265_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights530_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0066.cert531.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0066.cert531.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry265_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry265_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights531_linked j (List.mem_finRange j))
theorem actual_frozen_frame265 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame265 (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.flow.timeParameter_mem child_geometry265_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights265 hz)
theorem r_profile266_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.r266=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0033.r266.bounds := by rfl
theorem a_profile266_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.a266=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0033.a266.bounds := by rfl
theorem r_fixed266_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.r266.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r266.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r266.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r266.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed 7 := by decide +kernel
theorem a_fixed266_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.a266.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.a266.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed 9 := by decide +kernel
theorem ranks266_linked : ReferenceRankData.CoarseLowerShape.Batch0033.targetR266=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0033.targetA266=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed 1 := by decide +kernel
theorem r_input266_linked : ReferenceRankData.CoarseLowerShape.Batch0033.r266.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0033.r266.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0033.r266.bounds.gauge] := by decide +kernel
theorem a_input266_linked : ReferenceRankData.CoarseLowerShape.Batch0033.a266.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0033.a266.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0033.a266.bounds.gauge] := by decide +kernel
theorem geometry266_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.right.a := by decide +kernel
theorem weights532_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0066.cert532.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights533_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0066.cert533.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time266_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed 10)=true := by decide +kernel
theorem r_reference266_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed 0)=true := by decide +kernel
theorem a_reference266_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed 1)=true := by decide +kernel
theorem rank_r_link266_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0033.r266.bounds ReferenceRankData.CoarseLowerShape.Batch0033.r266 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link266_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0033.a266.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a266 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints266 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell true ReferenceProfileData.CoarseLowerShape.Batch0033.r266.bounds ReferenceRankData.CoarseLowerShape.Batch0033.r266 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile266_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0033.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0033.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link266_checked
    geometry266_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell false ReferenceProfileData.CoarseLowerShape.Batch0033.a266.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a266 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile266_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0033.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0033.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link266_checked
    geometry266_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks266_linked.1,←ranks266_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0033.r266.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a266.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0033.ordered266_checked hr ha ho
theorem frozen_frame266 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266 ReferenceProfileData.CoarseLowerShape.Batch0033.r266.bounds ReferenceProfileData.CoarseLowerShape.Batch0033.a266.bounds
  · rw [←r_profile266_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile266_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry266_linked.2.2.2.2.1
  · exact geometry266_linked.2.2.2.2.2
  · exact r_reference266_checked
  · exact a_reference266_checked
  · exact r_fixed266_linked
  · exact a_fixed266_linked
  · exact time266_checked
  · exact ht
  · exact hw
theorem child_geometry266_checked : ReferenceWeightData.CoarseLowerShape.Batch0066.cert532.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0066.cert532.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0066.cert533.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0066.cert533.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights266 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0066.cert532∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch66_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0066.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0066.cert533∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch66_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0066.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0066.cert532.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0066.cert532.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0066.cert532.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry266_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights532_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0066.cert533.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0066.cert533.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry266_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry266_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights533_linked j (List.mem_finRange j))
theorem actual_frozen_frame266 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame266 (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.flow.timeParameter_mem child_geometry266_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights266 hz)
theorem r_profile267_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.r267=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0033.r267.bounds := by rfl
theorem a_profile267_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.a267=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0033.a267.bounds := by rfl
theorem r_fixed267_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.r267.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r267.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r267.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r267.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed 7 := by decide +kernel
theorem a_fixed267_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.a267.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.a267.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed 9 := by decide +kernel
theorem ranks267_linked : ReferenceRankData.CoarseLowerShape.Batch0033.targetR267=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0033.targetA267=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed 1 := by decide +kernel
theorem r_input267_linked : ReferenceRankData.CoarseLowerShape.Batch0033.r267.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0033.r267.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0033.r267.bounds.gauge] := by decide +kernel
theorem a_input267_linked : ReferenceRankData.CoarseLowerShape.Batch0033.a267.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0033.a267.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0033.a267.bounds.gauge] := by decide +kernel
theorem geometry267_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.right.a := by decide +kernel
theorem weights534_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0066.cert534.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights535_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0066.cert535.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time267_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed 10)=true := by decide +kernel
theorem r_reference267_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed 0)=true := by decide +kernel
theorem a_reference267_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed 1)=true := by decide +kernel
theorem rank_r_link267_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0033.r267.bounds ReferenceRankData.CoarseLowerShape.Batch0033.r267 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link267_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0033.a267.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a267 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints267 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell true ReferenceProfileData.CoarseLowerShape.Batch0033.r267.bounds ReferenceRankData.CoarseLowerShape.Batch0033.r267 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile267_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0033.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0033.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link267_checked
    geometry267_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell false ReferenceProfileData.CoarseLowerShape.Batch0033.a267.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a267 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile267_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0033.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0033.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link267_checked
    geometry267_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks267_linked.1,←ranks267_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0033.r267.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a267.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0033.ordered267_checked hr ha ho
theorem frozen_frame267 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267 ReferenceProfileData.CoarseLowerShape.Batch0033.r267.bounds ReferenceProfileData.CoarseLowerShape.Batch0033.a267.bounds
  · rw [←r_profile267_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile267_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry267_linked.2.2.2.2.1
  · exact geometry267_linked.2.2.2.2.2
  · exact r_reference267_checked
  · exact a_reference267_checked
  · exact r_fixed267_linked
  · exact a_fixed267_linked
  · exact time267_checked
  · exact ht
  · exact hw
theorem child_geometry267_checked : ReferenceWeightData.CoarseLowerShape.Batch0066.cert534.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0066.cert534.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0066.cert535.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0066.cert535.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights267 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0066.cert534∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch66_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0066.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0066.cert535∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch66_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0066.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0066.cert534.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0066.cert534.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0066.cert534.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry267_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights534_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0066.cert535.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0066.cert535.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry267_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry267_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights535_linked j (List.mem_finRange j))
theorem actual_frozen_frame267 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame267 (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.flow.timeParameter_mem child_geometry267_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights267 hz)
theorem r_profile268_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.r268=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0033.r268.bounds := by rfl
theorem a_profile268_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.a268=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0033.a268.bounds := by rfl
theorem r_fixed268_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.r268.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r268.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r268.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r268.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed 7 := by decide +kernel
theorem a_fixed268_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.a268.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.a268.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed 9 := by decide +kernel
theorem ranks268_linked : ReferenceRankData.CoarseLowerShape.Batch0033.targetR268=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0033.targetA268=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed 1 := by decide +kernel
theorem r_input268_linked : ReferenceRankData.CoarseLowerShape.Batch0033.r268.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0033.r268.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0033.r268.bounds.gauge] := by decide +kernel
theorem a_input268_linked : ReferenceRankData.CoarseLowerShape.Batch0033.a268.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0033.a268.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0033.a268.bounds.gauge] := by decide +kernel
theorem geometry268_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.right.a := by decide +kernel
theorem weights536_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0067.cert536.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights537_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0067.cert537.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time268_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed 10)=true := by decide +kernel
theorem r_reference268_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed 0)=true := by decide +kernel
theorem a_reference268_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed 1)=true := by decide +kernel
theorem rank_r_link268_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0033.r268.bounds ReferenceRankData.CoarseLowerShape.Batch0033.r268 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link268_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0033.a268.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a268 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints268 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell true ReferenceProfileData.CoarseLowerShape.Batch0033.r268.bounds ReferenceRankData.CoarseLowerShape.Batch0033.r268 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile268_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0033.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0033.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link268_checked
    geometry268_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell false ReferenceProfileData.CoarseLowerShape.Batch0033.a268.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a268 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile268_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0033.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0033.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link268_checked
    geometry268_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks268_linked.1,←ranks268_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0033.r268.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a268.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0033.ordered268_checked hr ha ho
theorem frozen_frame268 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268 ReferenceProfileData.CoarseLowerShape.Batch0033.r268.bounds ReferenceProfileData.CoarseLowerShape.Batch0033.a268.bounds
  · rw [←r_profile268_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile268_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry268_linked.2.2.2.2.1
  · exact geometry268_linked.2.2.2.2.2
  · exact r_reference268_checked
  · exact a_reference268_checked
  · exact r_fixed268_linked
  · exact a_fixed268_linked
  · exact time268_checked
  · exact ht
  · exact hw
theorem child_geometry268_checked : ReferenceWeightData.CoarseLowerShape.Batch0067.cert536.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0067.cert536.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0067.cert537.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0067.cert537.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights268 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0067.cert536∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch67_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0067.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0067.cert537∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch67_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0067.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0067.cert536.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0067.cert536.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0067.cert536.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry268_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights536_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0067.cert537.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0067.cert537.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry268_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry268_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights537_linked j (List.mem_finRange j))
theorem actual_frozen_frame268 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame268 (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.flow.timeParameter_mem child_geometry268_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights268 hz)
theorem r_profile269_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.r269=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0033.r269.bounds := by rfl
theorem a_profile269_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.a269=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0033.a269.bounds := by rfl
theorem r_fixed269_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.r269.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r269.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r269.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r269.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed 7 := by decide +kernel
theorem a_fixed269_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.a269.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.a269.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed 9 := by decide +kernel
theorem ranks269_linked : ReferenceRankData.CoarseLowerShape.Batch0033.targetR269=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0033.targetA269=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed 1 := by decide +kernel
theorem r_input269_linked : ReferenceRankData.CoarseLowerShape.Batch0033.r269.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0033.r269.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0033.r269.bounds.gauge] := by decide +kernel
theorem a_input269_linked : ReferenceRankData.CoarseLowerShape.Batch0033.a269.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0033.a269.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0033.a269.bounds.gauge] := by decide +kernel
theorem geometry269_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.right.a := by decide +kernel
theorem weights538_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0067.cert538.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights539_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0067.cert539.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time269_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed 10)=true := by decide +kernel
theorem r_reference269_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed 0)=true := by decide +kernel
theorem a_reference269_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed 1)=true := by decide +kernel
theorem rank_r_link269_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0033.r269.bounds ReferenceRankData.CoarseLowerShape.Batch0033.r269 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link269_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0033.a269.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a269 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints269 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell true ReferenceProfileData.CoarseLowerShape.Batch0033.r269.bounds ReferenceRankData.CoarseLowerShape.Batch0033.r269 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile269_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0033.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0033.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link269_checked
    geometry269_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell false ReferenceProfileData.CoarseLowerShape.Batch0033.a269.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a269 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile269_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0033.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0033.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link269_checked
    geometry269_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks269_linked.1,←ranks269_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0033.r269.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a269.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0033.ordered269_checked hr ha ho
theorem frozen_frame269 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269 ReferenceProfileData.CoarseLowerShape.Batch0033.r269.bounds ReferenceProfileData.CoarseLowerShape.Batch0033.a269.bounds
  · rw [←r_profile269_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile269_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry269_linked.2.2.2.2.1
  · exact geometry269_linked.2.2.2.2.2
  · exact r_reference269_checked
  · exact a_reference269_checked
  · exact r_fixed269_linked
  · exact a_fixed269_linked
  · exact time269_checked
  · exact ht
  · exact hw
theorem child_geometry269_checked : ReferenceWeightData.CoarseLowerShape.Batch0067.cert538.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0067.cert538.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0067.cert539.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0067.cert539.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights269 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0067.cert538∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch67_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0067.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0067.cert539∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch67_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0067.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0067.cert538.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0067.cert538.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0067.cert538.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry269_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights538_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0067.cert539.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0067.cert539.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry269_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry269_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights539_linked j (List.mem_finRange j))
theorem actual_frozen_frame269 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame269 (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.flow.timeParameter_mem child_geometry269_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights269 hz)
theorem r_profile270_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.r270=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0033.r270.bounds := by rfl
theorem a_profile270_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.a270=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0033.a270.bounds := by rfl
theorem r_fixed270_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.r270.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r270.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r270.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r270.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed 7 := by decide +kernel
theorem a_fixed270_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.a270.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.a270.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed 9 := by decide +kernel
theorem ranks270_linked : ReferenceRankData.CoarseLowerShape.Batch0033.targetR270=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0033.targetA270=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed 1 := by decide +kernel
theorem r_input270_linked : ReferenceRankData.CoarseLowerShape.Batch0033.r270.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0033.r270.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0033.r270.bounds.gauge] := by decide +kernel
theorem a_input270_linked : ReferenceRankData.CoarseLowerShape.Batch0033.a270.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0033.a270.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0033.a270.bounds.gauge] := by decide +kernel
theorem geometry270_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.right.a := by decide +kernel
theorem weights540_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0067.cert540.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights541_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0067.cert541.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time270_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed 10)=true := by decide +kernel
theorem r_reference270_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed 0)=true := by decide +kernel
theorem a_reference270_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed 1)=true := by decide +kernel
theorem rank_r_link270_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0033.r270.bounds ReferenceRankData.CoarseLowerShape.Batch0033.r270 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link270_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0033.a270.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a270 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints270 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell true ReferenceProfileData.CoarseLowerShape.Batch0033.r270.bounds ReferenceRankData.CoarseLowerShape.Batch0033.r270 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile270_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0033.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0033.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link270_checked
    geometry270_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell false ReferenceProfileData.CoarseLowerShape.Batch0033.a270.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a270 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile270_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0033.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0033.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link270_checked
    geometry270_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks270_linked.1,←ranks270_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0033.r270.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a270.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0033.ordered270_checked hr ha ho
theorem frozen_frame270 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270 ReferenceProfileData.CoarseLowerShape.Batch0033.r270.bounds ReferenceProfileData.CoarseLowerShape.Batch0033.a270.bounds
  · rw [←r_profile270_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile270_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry270_linked.2.2.2.2.1
  · exact geometry270_linked.2.2.2.2.2
  · exact r_reference270_checked
  · exact a_reference270_checked
  · exact r_fixed270_linked
  · exact a_fixed270_linked
  · exact time270_checked
  · exact ht
  · exact hw
theorem child_geometry270_checked : ReferenceWeightData.CoarseLowerShape.Batch0067.cert540.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0067.cert540.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0067.cert541.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0067.cert541.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights270 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0067.cert540∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch67_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0067.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0067.cert541∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch67_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0067.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0067.cert540.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0067.cert540.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0067.cert540.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry270_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights540_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0067.cert541.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0067.cert541.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry270_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry270_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights541_linked j (List.mem_finRange j))
theorem actual_frozen_frame270 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame270 (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.flow.timeParameter_mem child_geometry270_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights270 hz)
theorem r_profile271_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.r271=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0033.r271.bounds := by rfl
theorem a_profile271_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.a271=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0033.a271.bounds := by rfl
theorem r_fixed271_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.r271.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r271.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r271.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.r271.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed 7 := by decide +kernel
theorem a_fixed271_linked : ReferenceProfileData.CoarseLowerShape.Batch0033.a271.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0033.a271.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed 9 := by decide +kernel
theorem ranks271_linked : ReferenceRankData.CoarseLowerShape.Batch0033.targetR271=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0033.targetA271=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed 1 := by decide +kernel
theorem r_input271_linked : ReferenceRankData.CoarseLowerShape.Batch0033.r271.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0033.r271.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0033.r271.bounds.gauge] := by decide +kernel
theorem a_input271_linked : ReferenceRankData.CoarseLowerShape.Batch0033.a271.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0033.a271.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0033.a271.bounds.gauge] := by decide +kernel
theorem geometry271_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.right.a := by decide +kernel
theorem weights542_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0067.cert542.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights543_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0067.cert543.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time271_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed 10)=true := by decide +kernel
theorem r_reference271_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed 0)=true := by decide +kernel
theorem a_reference271_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed 1)=true := by decide +kernel
theorem rank_r_link271_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0033.r271.bounds ReferenceRankData.CoarseLowerShape.Batch0033.r271 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link271_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0033.a271.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a271 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints271 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell true ReferenceProfileData.CoarseLowerShape.Batch0033.r271.bounds ReferenceRankData.CoarseLowerShape.Batch0033.r271 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile271_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0033.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0033.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link271_checked
    geometry271_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell false ReferenceProfileData.CoarseLowerShape.Batch0033.a271.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a271 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile271_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0033.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0033.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link271_checked
    geometry271_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks271_linked.1,←ranks271_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0033.r271.bounds ReferenceRankData.CoarseLowerShape.Batch0033.a271.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0033.ordered271_checked hr ha ho
theorem frozen_frame271 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271 ReferenceProfileData.CoarseLowerShape.Batch0033.r271.bounds ReferenceProfileData.CoarseLowerShape.Batch0033.a271.bounds
  · rw [←r_profile271_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile271_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry271_linked.2.2.2.2.1
  · exact geometry271_linked.2.2.2.2.2
  · exact r_reference271_checked
  · exact a_reference271_checked
  · exact r_fixed271_linked
  · exact a_fixed271_linked
  · exact time271_checked
  · exact ht
  · exact hw
theorem child_geometry271_checked : ReferenceWeightData.CoarseLowerShape.Batch0067.cert542.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0067.cert542.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0067.cert543.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0067.cert543.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights271 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0067.cert542∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch67_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0067.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0067.cert543∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch67_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0067.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0067.cert542.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0067.cert542.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0067.cert542.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry271_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights542_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0067.cert543.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0067.cert543.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry271_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry271_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights543_linked j (List.mem_finRange j))
theorem actual_frozen_frame271 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame271 (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.flow.timeParameter_mem child_geometry271_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights271 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell264),(ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell265),(ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell266),(ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell267),(ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell268),(ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell269),(ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell270),(ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0033.cell271)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0033.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0033.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame264 hz
  · exact fun z hz=>actual_frozen_frame265 hz
  · exact fun z hz=>actual_frozen_frame266 hz
  · exact fun z hz=>actual_frozen_frame267 hz
  · exact fun z hz=>actual_frozen_frame268 hz
  · exact fun z hz=>actual_frozen_frame269 hz
  · exact fun z hz=>actual_frozen_frame270 hz
  · exact fun z hz=>actual_frozen_frame271 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints264 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints265 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints266 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints267 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints268 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints269 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints270 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints271 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry264_linked.1,geometry264_linked.2.1,geometry264_linked.2.2.1,geometry264_linked.2.2.2.1⟩
  · exact ⟨geometry265_linked.1,geometry265_linked.2.1,geometry265_linked.2.2.1,geometry265_linked.2.2.2.1⟩
  · exact ⟨geometry266_linked.1,geometry266_linked.2.1,geometry266_linked.2.2.1,geometry266_linked.2.2.2.1⟩
  · exact ⟨geometry267_linked.1,geometry267_linked.2.1,geometry267_linked.2.2.1,geometry267_linked.2.2.2.1⟩
  · exact ⟨geometry268_linked.1,geometry268_linked.2.1,geometry268_linked.2.2.1,geometry268_linked.2.2.2.1⟩
  · exact ⟨geometry269_linked.1,geometry269_linked.2.1,geometry269_linked.2.2.1,geometry269_linked.2.2.2.1⟩
  · exact ⟨geometry270_linked.1,geometry270_linked.2.1,geometry270_linked.2.2.1,geometry270_linked.2.2.2.1⟩
  · exact ⟨geometry271_linked.1,geometry271_linked.2.1,geometry271_linked.2.2.1,geometry271_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0033.a264.bounds,?_,geometry264_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0033.a264.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile264_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0033.r264.bounds,?_,geometry264_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert264.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0033.r264.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile264_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0033.a265.bounds,?_,geometry265_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0033.a265.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile265_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0033.r265.bounds,?_,geometry265_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert265.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0033.r265.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile265_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0033.a266.bounds,?_,geometry266_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0033.a266.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile266_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0033.r266.bounds,?_,geometry266_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert266.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0033.r266.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile266_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0033.a267.bounds,?_,geometry267_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0033.a267.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile267_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0033.r267.bounds,?_,geometry267_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert267.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0033.r267.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile267_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0033.a268.bounds,?_,geometry268_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0033.a268.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile268_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0033.r268.bounds,?_,geometry268_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert268.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0033.r268.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile268_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0033.a269.bounds,?_,geometry269_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0033.a269.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile269_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0033.r269.bounds,?_,geometry269_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert269.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0033.r269.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile269_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0033.a270.bounds,?_,geometry270_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0033.a270.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile270_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0033.r270.bounds,?_,geometry270_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert270.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0033.r270.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile270_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0033.a271.bounds,?_,geometry271_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0033.a271.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile271_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0033.r271.bounds,?_,geometry271_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0033.cert271.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0033.r271.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile271_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0033.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0033.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0033

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0034
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch68_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0068.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0068.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch69_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0069.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0069.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile272_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.r272=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0034.r272.bounds := by rfl
theorem a_profile272_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.a272=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0034.a272.bounds := by rfl
theorem r_fixed272_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.r272.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r272.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r272.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r272.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed 7 := by decide +kernel
theorem a_fixed272_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.a272.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.a272.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed 9 := by decide +kernel
theorem ranks272_linked : ReferenceRankData.CoarseLowerShape.Batch0034.targetR272=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0034.targetA272=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed 1 := by decide +kernel
theorem r_input272_linked : ReferenceRankData.CoarseLowerShape.Batch0034.r272.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0034.r272.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0034.r272.bounds.gauge] := by decide +kernel
theorem a_input272_linked : ReferenceRankData.CoarseLowerShape.Batch0034.a272.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0034.a272.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0034.a272.bounds.gauge] := by decide +kernel
theorem geometry272_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.right.a := by decide +kernel
theorem weights544_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0068.cert544.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights545_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0068.cert545.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time272_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed 10)=true := by decide +kernel
theorem r_reference272_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed 0)=true := by decide +kernel
theorem a_reference272_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed 1)=true := by decide +kernel
theorem rank_r_link272_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0034.r272.bounds ReferenceRankData.CoarseLowerShape.Batch0034.r272 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link272_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0034.a272.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a272 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints272 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell true ReferenceProfileData.CoarseLowerShape.Batch0034.r272.bounds ReferenceRankData.CoarseLowerShape.Batch0034.r272 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile272_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0034.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0034.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link272_checked
    geometry272_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell false ReferenceProfileData.CoarseLowerShape.Batch0034.a272.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a272 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile272_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0034.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0034.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link272_checked
    geometry272_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks272_linked.1,←ranks272_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0034.r272.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a272.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0034.ordered272_checked hr ha ho
theorem frozen_frame272 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272 ReferenceProfileData.CoarseLowerShape.Batch0034.r272.bounds ReferenceProfileData.CoarseLowerShape.Batch0034.a272.bounds
  · rw [←r_profile272_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile272_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry272_linked.2.2.2.2.1
  · exact geometry272_linked.2.2.2.2.2
  · exact r_reference272_checked
  · exact a_reference272_checked
  · exact r_fixed272_linked
  · exact a_fixed272_linked
  · exact time272_checked
  · exact ht
  · exact hw
theorem child_geometry272_checked : ReferenceWeightData.CoarseLowerShape.Batch0068.cert544.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0068.cert544.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0068.cert545.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0068.cert545.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights272 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0068.cert544∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch68_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0068.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0068.cert545∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch68_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0068.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0068.cert544.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0068.cert544.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0068.cert544.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry272_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights544_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0068.cert545.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0068.cert545.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry272_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry272_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights545_linked j (List.mem_finRange j))
theorem actual_frozen_frame272 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame272 (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.flow.timeParameter_mem child_geometry272_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights272 hz)
theorem r_profile273_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.r273=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0034.r273.bounds := by rfl
theorem a_profile273_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.a273=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0034.a273.bounds := by rfl
theorem r_fixed273_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.r273.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r273.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r273.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r273.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed 7 := by decide +kernel
theorem a_fixed273_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.a273.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.a273.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed 9 := by decide +kernel
theorem ranks273_linked : ReferenceRankData.CoarseLowerShape.Batch0034.targetR273=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0034.targetA273=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed 1 := by decide +kernel
theorem r_input273_linked : ReferenceRankData.CoarseLowerShape.Batch0034.r273.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0034.r273.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0034.r273.bounds.gauge] := by decide +kernel
theorem a_input273_linked : ReferenceRankData.CoarseLowerShape.Batch0034.a273.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0034.a273.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0034.a273.bounds.gauge] := by decide +kernel
theorem geometry273_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.right.a := by decide +kernel
theorem weights546_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0068.cert546.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights547_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0068.cert547.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time273_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed 10)=true := by decide +kernel
theorem r_reference273_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed 0)=true := by decide +kernel
theorem a_reference273_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed 1)=true := by decide +kernel
theorem rank_r_link273_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0034.r273.bounds ReferenceRankData.CoarseLowerShape.Batch0034.r273 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link273_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0034.a273.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a273 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints273 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell true ReferenceProfileData.CoarseLowerShape.Batch0034.r273.bounds ReferenceRankData.CoarseLowerShape.Batch0034.r273 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile273_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0034.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0034.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link273_checked
    geometry273_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell false ReferenceProfileData.CoarseLowerShape.Batch0034.a273.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a273 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile273_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0034.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0034.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link273_checked
    geometry273_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks273_linked.1,←ranks273_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0034.r273.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a273.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0034.ordered273_checked hr ha ho
theorem frozen_frame273 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273 ReferenceProfileData.CoarseLowerShape.Batch0034.r273.bounds ReferenceProfileData.CoarseLowerShape.Batch0034.a273.bounds
  · rw [←r_profile273_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile273_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry273_linked.2.2.2.2.1
  · exact geometry273_linked.2.2.2.2.2
  · exact r_reference273_checked
  · exact a_reference273_checked
  · exact r_fixed273_linked
  · exact a_fixed273_linked
  · exact time273_checked
  · exact ht
  · exact hw
theorem child_geometry273_checked : ReferenceWeightData.CoarseLowerShape.Batch0068.cert546.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0068.cert546.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0068.cert547.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0068.cert547.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights273 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0068.cert546∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch68_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0068.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0068.cert547∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch68_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0068.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0068.cert546.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0068.cert546.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0068.cert546.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry273_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights546_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0068.cert547.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0068.cert547.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry273_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry273_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights547_linked j (List.mem_finRange j))
theorem actual_frozen_frame273 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame273 (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.flow.timeParameter_mem child_geometry273_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights273 hz)
theorem r_profile274_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.r274=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0034.r274.bounds := by rfl
theorem a_profile274_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.a274=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0034.a274.bounds := by rfl
theorem r_fixed274_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.r274.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r274.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r274.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r274.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed 7 := by decide +kernel
theorem a_fixed274_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.a274.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.a274.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed 9 := by decide +kernel
theorem ranks274_linked : ReferenceRankData.CoarseLowerShape.Batch0034.targetR274=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0034.targetA274=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed 1 := by decide +kernel
theorem r_input274_linked : ReferenceRankData.CoarseLowerShape.Batch0034.r274.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0034.r274.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0034.r274.bounds.gauge] := by decide +kernel
theorem a_input274_linked : ReferenceRankData.CoarseLowerShape.Batch0034.a274.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0034.a274.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0034.a274.bounds.gauge] := by decide +kernel
theorem geometry274_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.right.a := by decide +kernel
theorem weights548_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0068.cert548.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights549_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0068.cert549.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time274_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed 10)=true := by decide +kernel
theorem r_reference274_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed 0)=true := by decide +kernel
theorem a_reference274_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed 1)=true := by decide +kernel
theorem rank_r_link274_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0034.r274.bounds ReferenceRankData.CoarseLowerShape.Batch0034.r274 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link274_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0034.a274.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a274 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints274 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell true ReferenceProfileData.CoarseLowerShape.Batch0034.r274.bounds ReferenceRankData.CoarseLowerShape.Batch0034.r274 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile274_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0034.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0034.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link274_checked
    geometry274_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell false ReferenceProfileData.CoarseLowerShape.Batch0034.a274.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a274 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile274_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0034.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0034.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link274_checked
    geometry274_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks274_linked.1,←ranks274_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0034.r274.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a274.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0034.ordered274_checked hr ha ho
theorem frozen_frame274 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274 ReferenceProfileData.CoarseLowerShape.Batch0034.r274.bounds ReferenceProfileData.CoarseLowerShape.Batch0034.a274.bounds
  · rw [←r_profile274_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile274_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry274_linked.2.2.2.2.1
  · exact geometry274_linked.2.2.2.2.2
  · exact r_reference274_checked
  · exact a_reference274_checked
  · exact r_fixed274_linked
  · exact a_fixed274_linked
  · exact time274_checked
  · exact ht
  · exact hw
theorem child_geometry274_checked : ReferenceWeightData.CoarseLowerShape.Batch0068.cert548.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0068.cert548.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0068.cert549.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0068.cert549.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights274 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0068.cert548∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch68_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0068.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0068.cert549∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch68_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0068.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0068.cert548.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0068.cert548.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0068.cert548.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry274_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights548_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0068.cert549.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0068.cert549.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry274_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry274_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights549_linked j (List.mem_finRange j))
theorem actual_frozen_frame274 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame274 (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.flow.timeParameter_mem child_geometry274_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights274 hz)
theorem r_profile275_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.r275=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0034.r275.bounds := by rfl
theorem a_profile275_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.a275=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0034.a275.bounds := by rfl
theorem r_fixed275_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.r275.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r275.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r275.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r275.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed 7 := by decide +kernel
theorem a_fixed275_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.a275.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.a275.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed 9 := by decide +kernel
theorem ranks275_linked : ReferenceRankData.CoarseLowerShape.Batch0034.targetR275=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0034.targetA275=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed 1 := by decide +kernel
theorem r_input275_linked : ReferenceRankData.CoarseLowerShape.Batch0034.r275.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0034.r275.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0034.r275.bounds.gauge] := by decide +kernel
theorem a_input275_linked : ReferenceRankData.CoarseLowerShape.Batch0034.a275.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0034.a275.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0034.a275.bounds.gauge] := by decide +kernel
theorem geometry275_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.right.a := by decide +kernel
theorem weights550_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0068.cert550.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights551_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0068.cert551.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time275_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed 10)=true := by decide +kernel
theorem r_reference275_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed 0)=true := by decide +kernel
theorem a_reference275_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed 1)=true := by decide +kernel
theorem rank_r_link275_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0034.r275.bounds ReferenceRankData.CoarseLowerShape.Batch0034.r275 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link275_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0034.a275.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a275 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints275 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell true ReferenceProfileData.CoarseLowerShape.Batch0034.r275.bounds ReferenceRankData.CoarseLowerShape.Batch0034.r275 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile275_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0034.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0034.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link275_checked
    geometry275_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell false ReferenceProfileData.CoarseLowerShape.Batch0034.a275.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a275 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile275_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0034.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0034.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link275_checked
    geometry275_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks275_linked.1,←ranks275_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0034.r275.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a275.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0034.ordered275_checked hr ha ho
theorem frozen_frame275 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275 ReferenceProfileData.CoarseLowerShape.Batch0034.r275.bounds ReferenceProfileData.CoarseLowerShape.Batch0034.a275.bounds
  · rw [←r_profile275_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile275_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry275_linked.2.2.2.2.1
  · exact geometry275_linked.2.2.2.2.2
  · exact r_reference275_checked
  · exact a_reference275_checked
  · exact r_fixed275_linked
  · exact a_fixed275_linked
  · exact time275_checked
  · exact ht
  · exact hw
theorem child_geometry275_checked : ReferenceWeightData.CoarseLowerShape.Batch0068.cert550.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0068.cert550.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0068.cert551.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0068.cert551.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights275 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0068.cert550∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch68_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0068.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0068.cert551∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch68_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0068.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0068.cert550.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0068.cert550.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0068.cert550.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry275_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights550_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0068.cert551.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0068.cert551.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry275_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry275_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights551_linked j (List.mem_finRange j))
theorem actual_frozen_frame275 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame275 (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.flow.timeParameter_mem child_geometry275_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights275 hz)
theorem r_profile276_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.r276=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0034.r276.bounds := by rfl
theorem a_profile276_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.a276=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0034.a276.bounds := by rfl
theorem r_fixed276_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.r276.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r276.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r276.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r276.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed 7 := by decide +kernel
theorem a_fixed276_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.a276.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.a276.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed 9 := by decide +kernel
theorem ranks276_linked : ReferenceRankData.CoarseLowerShape.Batch0034.targetR276=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0034.targetA276=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed 1 := by decide +kernel
theorem r_input276_linked : ReferenceRankData.CoarseLowerShape.Batch0034.r276.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0034.r276.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0034.r276.bounds.gauge] := by decide +kernel
theorem a_input276_linked : ReferenceRankData.CoarseLowerShape.Batch0034.a276.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0034.a276.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0034.a276.bounds.gauge] := by decide +kernel
theorem geometry276_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.right.a := by decide +kernel
theorem weights552_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0069.cert552.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights553_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0069.cert553.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time276_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed 10)=true := by decide +kernel
theorem r_reference276_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed 0)=true := by decide +kernel
theorem a_reference276_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed 1)=true := by decide +kernel
theorem rank_r_link276_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0034.r276.bounds ReferenceRankData.CoarseLowerShape.Batch0034.r276 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link276_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0034.a276.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a276 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints276 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell true ReferenceProfileData.CoarseLowerShape.Batch0034.r276.bounds ReferenceRankData.CoarseLowerShape.Batch0034.r276 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile276_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0034.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0034.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link276_checked
    geometry276_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell false ReferenceProfileData.CoarseLowerShape.Batch0034.a276.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a276 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile276_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0034.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0034.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link276_checked
    geometry276_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks276_linked.1,←ranks276_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0034.r276.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a276.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0034.ordered276_checked hr ha ho
theorem frozen_frame276 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276 ReferenceProfileData.CoarseLowerShape.Batch0034.r276.bounds ReferenceProfileData.CoarseLowerShape.Batch0034.a276.bounds
  · rw [←r_profile276_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile276_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry276_linked.2.2.2.2.1
  · exact geometry276_linked.2.2.2.2.2
  · exact r_reference276_checked
  · exact a_reference276_checked
  · exact r_fixed276_linked
  · exact a_fixed276_linked
  · exact time276_checked
  · exact ht
  · exact hw
theorem child_geometry276_checked : ReferenceWeightData.CoarseLowerShape.Batch0069.cert552.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0069.cert552.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0069.cert553.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0069.cert553.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights276 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0069.cert552∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch69_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0069.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0069.cert553∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch69_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0069.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0069.cert552.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0069.cert552.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0069.cert552.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry276_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights552_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0069.cert553.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0069.cert553.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry276_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry276_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights553_linked j (List.mem_finRange j))
theorem actual_frozen_frame276 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame276 (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.flow.timeParameter_mem child_geometry276_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights276 hz)
theorem r_profile277_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.r277=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0034.r277.bounds := by rfl
theorem a_profile277_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.a277=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0034.a277.bounds := by rfl
theorem r_fixed277_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.r277.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r277.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r277.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r277.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed 7 := by decide +kernel
theorem a_fixed277_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.a277.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.a277.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed 9 := by decide +kernel
theorem ranks277_linked : ReferenceRankData.CoarseLowerShape.Batch0034.targetR277=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0034.targetA277=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed 1 := by decide +kernel
theorem r_input277_linked : ReferenceRankData.CoarseLowerShape.Batch0034.r277.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0034.r277.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0034.r277.bounds.gauge] := by decide +kernel
theorem a_input277_linked : ReferenceRankData.CoarseLowerShape.Batch0034.a277.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0034.a277.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0034.a277.bounds.gauge] := by decide +kernel
theorem geometry277_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.right.a := by decide +kernel
theorem weights554_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0069.cert554.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights555_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0069.cert555.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time277_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed 10)=true := by decide +kernel
theorem r_reference277_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed 0)=true := by decide +kernel
theorem a_reference277_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed 1)=true := by decide +kernel
theorem rank_r_link277_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0034.r277.bounds ReferenceRankData.CoarseLowerShape.Batch0034.r277 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link277_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0034.a277.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a277 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints277 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell true ReferenceProfileData.CoarseLowerShape.Batch0034.r277.bounds ReferenceRankData.CoarseLowerShape.Batch0034.r277 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile277_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0034.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0034.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link277_checked
    geometry277_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell false ReferenceProfileData.CoarseLowerShape.Batch0034.a277.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a277 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile277_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0034.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0034.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link277_checked
    geometry277_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks277_linked.1,←ranks277_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0034.r277.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a277.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0034.ordered277_checked hr ha ho
theorem frozen_frame277 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277 ReferenceProfileData.CoarseLowerShape.Batch0034.r277.bounds ReferenceProfileData.CoarseLowerShape.Batch0034.a277.bounds
  · rw [←r_profile277_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile277_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry277_linked.2.2.2.2.1
  · exact geometry277_linked.2.2.2.2.2
  · exact r_reference277_checked
  · exact a_reference277_checked
  · exact r_fixed277_linked
  · exact a_fixed277_linked
  · exact time277_checked
  · exact ht
  · exact hw
theorem child_geometry277_checked : ReferenceWeightData.CoarseLowerShape.Batch0069.cert554.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0069.cert554.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0069.cert555.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0069.cert555.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights277 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0069.cert554∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch69_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0069.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0069.cert555∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch69_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0069.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0069.cert554.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0069.cert554.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0069.cert554.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry277_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights554_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0069.cert555.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0069.cert555.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry277_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry277_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights555_linked j (List.mem_finRange j))
theorem actual_frozen_frame277 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame277 (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.flow.timeParameter_mem child_geometry277_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights277 hz)
theorem r_profile278_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.r278=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0034.r278.bounds := by rfl
theorem a_profile278_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.a278=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0034.a278.bounds := by rfl
theorem r_fixed278_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.r278.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r278.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r278.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r278.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed 7 := by decide +kernel
theorem a_fixed278_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.a278.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.a278.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed 9 := by decide +kernel
theorem ranks278_linked : ReferenceRankData.CoarseLowerShape.Batch0034.targetR278=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0034.targetA278=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed 1 := by decide +kernel
theorem r_input278_linked : ReferenceRankData.CoarseLowerShape.Batch0034.r278.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0034.r278.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0034.r278.bounds.gauge] := by decide +kernel
theorem a_input278_linked : ReferenceRankData.CoarseLowerShape.Batch0034.a278.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0034.a278.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0034.a278.bounds.gauge] := by decide +kernel
theorem geometry278_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.right.a := by decide +kernel
theorem weights556_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0069.cert556.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights557_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0069.cert557.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time278_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed 10)=true := by decide +kernel
theorem r_reference278_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed 0)=true := by decide +kernel
theorem a_reference278_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed 1)=true := by decide +kernel
theorem rank_r_link278_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0034.r278.bounds ReferenceRankData.CoarseLowerShape.Batch0034.r278 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link278_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0034.a278.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a278 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints278 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell true ReferenceProfileData.CoarseLowerShape.Batch0034.r278.bounds ReferenceRankData.CoarseLowerShape.Batch0034.r278 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile278_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0034.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0034.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link278_checked
    geometry278_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell false ReferenceProfileData.CoarseLowerShape.Batch0034.a278.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a278 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile278_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0034.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0034.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link278_checked
    geometry278_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks278_linked.1,←ranks278_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0034.r278.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a278.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0034.ordered278_checked hr ha ho
theorem frozen_frame278 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278 ReferenceProfileData.CoarseLowerShape.Batch0034.r278.bounds ReferenceProfileData.CoarseLowerShape.Batch0034.a278.bounds
  · rw [←r_profile278_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile278_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry278_linked.2.2.2.2.1
  · exact geometry278_linked.2.2.2.2.2
  · exact r_reference278_checked
  · exact a_reference278_checked
  · exact r_fixed278_linked
  · exact a_fixed278_linked
  · exact time278_checked
  · exact ht
  · exact hw
theorem child_geometry278_checked : ReferenceWeightData.CoarseLowerShape.Batch0069.cert556.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0069.cert556.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0069.cert557.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0069.cert557.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights278 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0069.cert556∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch69_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0069.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0069.cert557∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch69_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0069.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0069.cert556.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0069.cert556.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0069.cert556.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry278_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights556_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0069.cert557.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0069.cert557.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry278_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry278_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights557_linked j (List.mem_finRange j))
theorem actual_frozen_frame278 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame278 (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.flow.timeParameter_mem child_geometry278_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights278 hz)
theorem r_profile279_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.r279=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0034.r279.bounds := by rfl
theorem a_profile279_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.a279=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0034.a279.bounds := by rfl
theorem r_fixed279_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.r279.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r279.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r279.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.r279.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed 7 := by decide +kernel
theorem a_fixed279_linked : ReferenceProfileData.CoarseLowerShape.Batch0034.a279.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0034.a279.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed 9 := by decide +kernel
theorem ranks279_linked : ReferenceRankData.CoarseLowerShape.Batch0034.targetR279=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0034.targetA279=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed 1 := by decide +kernel
theorem r_input279_linked : ReferenceRankData.CoarseLowerShape.Batch0034.r279.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0034.r279.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0034.r279.bounds.gauge] := by decide +kernel
theorem a_input279_linked : ReferenceRankData.CoarseLowerShape.Batch0034.a279.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0034.a279.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0034.a279.bounds.gauge] := by decide +kernel
theorem geometry279_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.right.a := by decide +kernel
theorem weights558_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0069.cert558.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights559_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0069.cert559.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time279_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed 10)=true := by decide +kernel
theorem r_reference279_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed 0)=true := by decide +kernel
theorem a_reference279_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed 1)=true := by decide +kernel
theorem rank_r_link279_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0034.r279.bounds ReferenceRankData.CoarseLowerShape.Batch0034.r279 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link279_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0034.a279.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a279 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints279 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell true ReferenceProfileData.CoarseLowerShape.Batch0034.r279.bounds ReferenceRankData.CoarseLowerShape.Batch0034.r279 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile279_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0034.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0034.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link279_checked
    geometry279_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell false ReferenceProfileData.CoarseLowerShape.Batch0034.a279.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a279 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile279_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0034.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0034.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link279_checked
    geometry279_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks279_linked.1,←ranks279_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0034.r279.bounds ReferenceRankData.CoarseLowerShape.Batch0034.a279.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0034.ordered279_checked hr ha ho
theorem frozen_frame279 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279 ReferenceProfileData.CoarseLowerShape.Batch0034.r279.bounds ReferenceProfileData.CoarseLowerShape.Batch0034.a279.bounds
  · rw [←r_profile279_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile279_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry279_linked.2.2.2.2.1
  · exact geometry279_linked.2.2.2.2.2
  · exact r_reference279_checked
  · exact a_reference279_checked
  · exact r_fixed279_linked
  · exact a_fixed279_linked
  · exact time279_checked
  · exact ht
  · exact hw
theorem child_geometry279_checked : ReferenceWeightData.CoarseLowerShape.Batch0069.cert558.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0069.cert558.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0069.cert559.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0069.cert559.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights279 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0069.cert558∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch69_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0069.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0069.cert559∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch69_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0069.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0069.cert558.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0069.cert558.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0069.cert558.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry279_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights558_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0069.cert559.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0069.cert559.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry279_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry279_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights559_linked j (List.mem_finRange j))
theorem actual_frozen_frame279 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame279 (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.flow.timeParameter_mem child_geometry279_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights279 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell272),(ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell273),(ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell274),(ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell275),(ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell276),(ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell277),(ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell278),(ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0034.cell279)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0034.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0034.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame272 hz
  · exact fun z hz=>actual_frozen_frame273 hz
  · exact fun z hz=>actual_frozen_frame274 hz
  · exact fun z hz=>actual_frozen_frame275 hz
  · exact fun z hz=>actual_frozen_frame276 hz
  · exact fun z hz=>actual_frozen_frame277 hz
  · exact fun z hz=>actual_frozen_frame278 hz
  · exact fun z hz=>actual_frozen_frame279 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints272 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints273 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints274 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints275 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints276 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints277 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints278 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints279 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry272_linked.1,geometry272_linked.2.1,geometry272_linked.2.2.1,geometry272_linked.2.2.2.1⟩
  · exact ⟨geometry273_linked.1,geometry273_linked.2.1,geometry273_linked.2.2.1,geometry273_linked.2.2.2.1⟩
  · exact ⟨geometry274_linked.1,geometry274_linked.2.1,geometry274_linked.2.2.1,geometry274_linked.2.2.2.1⟩
  · exact ⟨geometry275_linked.1,geometry275_linked.2.1,geometry275_linked.2.2.1,geometry275_linked.2.2.2.1⟩
  · exact ⟨geometry276_linked.1,geometry276_linked.2.1,geometry276_linked.2.2.1,geometry276_linked.2.2.2.1⟩
  · exact ⟨geometry277_linked.1,geometry277_linked.2.1,geometry277_linked.2.2.1,geometry277_linked.2.2.2.1⟩
  · exact ⟨geometry278_linked.1,geometry278_linked.2.1,geometry278_linked.2.2.1,geometry278_linked.2.2.2.1⟩
  · exact ⟨geometry279_linked.1,geometry279_linked.2.1,geometry279_linked.2.2.1,geometry279_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0034.a272.bounds,?_,geometry272_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0034.a272.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile272_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0034.r272.bounds,?_,geometry272_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert272.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0034.r272.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile272_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0034.a273.bounds,?_,geometry273_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0034.a273.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile273_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0034.r273.bounds,?_,geometry273_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert273.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0034.r273.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile273_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0034.a274.bounds,?_,geometry274_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0034.a274.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile274_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0034.r274.bounds,?_,geometry274_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert274.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0034.r274.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile274_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0034.a275.bounds,?_,geometry275_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0034.a275.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile275_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0034.r275.bounds,?_,geometry275_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert275.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0034.r275.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile275_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0034.a276.bounds,?_,geometry276_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0034.a276.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile276_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0034.r276.bounds,?_,geometry276_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert276.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0034.r276.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile276_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0034.a277.bounds,?_,geometry277_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0034.a277.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile277_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0034.r277.bounds,?_,geometry277_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert277.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0034.r277.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile277_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0034.a278.bounds,?_,geometry278_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0034.a278.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile278_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0034.r278.bounds,?_,geometry278_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert278.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0034.r278.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile278_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0034.a279.bounds,?_,geometry279_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0034.a279.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile279_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0034.r279.bounds,?_,geometry279_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0034.cert279.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0034.r279.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile279_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0034.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0034.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0034

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0035
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch70_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0070.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0070.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch71_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0071.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0071.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile280_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.r280=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0035.r280.bounds := by rfl
theorem a_profile280_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.a280=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0035.a280.bounds := by rfl
theorem r_fixed280_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.r280.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r280.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r280.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r280.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed 7 := by decide +kernel
theorem a_fixed280_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.a280.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.a280.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed 9 := by decide +kernel
theorem ranks280_linked : ReferenceRankData.CoarseLowerShape.Batch0035.targetR280=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0035.targetA280=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed 1 := by decide +kernel
theorem r_input280_linked : ReferenceRankData.CoarseLowerShape.Batch0035.r280.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0035.r280.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0035.r280.bounds.gauge] := by decide +kernel
theorem a_input280_linked : ReferenceRankData.CoarseLowerShape.Batch0035.a280.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0035.a280.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0035.a280.bounds.gauge] := by decide +kernel
theorem geometry280_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.right.a := by decide +kernel
theorem weights560_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0070.cert560.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights561_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0070.cert561.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time280_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed 10)=true := by decide +kernel
theorem r_reference280_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed 0)=true := by decide +kernel
theorem a_reference280_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed 1)=true := by decide +kernel
theorem rank_r_link280_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0035.r280.bounds ReferenceRankData.CoarseLowerShape.Batch0035.r280 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link280_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0035.a280.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a280 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints280 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell true ReferenceProfileData.CoarseLowerShape.Batch0035.r280.bounds ReferenceRankData.CoarseLowerShape.Batch0035.r280 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile280_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0035.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0035.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link280_checked
    geometry280_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell false ReferenceProfileData.CoarseLowerShape.Batch0035.a280.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a280 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile280_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0035.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0035.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link280_checked
    geometry280_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks280_linked.1,←ranks280_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0035.r280.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a280.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0035.ordered280_checked hr ha ho
theorem frozen_frame280 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280 ReferenceProfileData.CoarseLowerShape.Batch0035.r280.bounds ReferenceProfileData.CoarseLowerShape.Batch0035.a280.bounds
  · rw [←r_profile280_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile280_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry280_linked.2.2.2.2.1
  · exact geometry280_linked.2.2.2.2.2
  · exact r_reference280_checked
  · exact a_reference280_checked
  · exact r_fixed280_linked
  · exact a_fixed280_linked
  · exact time280_checked
  · exact ht
  · exact hw
theorem child_geometry280_checked : ReferenceWeightData.CoarseLowerShape.Batch0070.cert560.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0070.cert560.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0070.cert561.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0070.cert561.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights280 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0070.cert560∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch70_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0070.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0070.cert561∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch70_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0070.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0070.cert560.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0070.cert560.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0070.cert560.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry280_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights560_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0070.cert561.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0070.cert561.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry280_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry280_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights561_linked j (List.mem_finRange j))
theorem actual_frozen_frame280 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame280 (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.flow.timeParameter_mem child_geometry280_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights280 hz)
theorem r_profile281_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.r281=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0035.r281.bounds := by rfl
theorem a_profile281_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.a281=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0035.a281.bounds := by rfl
theorem r_fixed281_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.r281.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r281.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r281.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r281.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed 7 := by decide +kernel
theorem a_fixed281_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.a281.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.a281.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed 9 := by decide +kernel
theorem ranks281_linked : ReferenceRankData.CoarseLowerShape.Batch0035.targetR281=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0035.targetA281=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed 1 := by decide +kernel
theorem r_input281_linked : ReferenceRankData.CoarseLowerShape.Batch0035.r281.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0035.r281.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0035.r281.bounds.gauge] := by decide +kernel
theorem a_input281_linked : ReferenceRankData.CoarseLowerShape.Batch0035.a281.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0035.a281.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0035.a281.bounds.gauge] := by decide +kernel
theorem geometry281_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.right.a := by decide +kernel
theorem weights562_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0070.cert562.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights563_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0070.cert563.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time281_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed 10)=true := by decide +kernel
theorem r_reference281_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed 0)=true := by decide +kernel
theorem a_reference281_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed 1)=true := by decide +kernel
theorem rank_r_link281_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0035.r281.bounds ReferenceRankData.CoarseLowerShape.Batch0035.r281 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link281_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0035.a281.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a281 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints281 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell true ReferenceProfileData.CoarseLowerShape.Batch0035.r281.bounds ReferenceRankData.CoarseLowerShape.Batch0035.r281 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile281_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0035.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0035.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link281_checked
    geometry281_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell false ReferenceProfileData.CoarseLowerShape.Batch0035.a281.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a281 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile281_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0035.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0035.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link281_checked
    geometry281_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks281_linked.1,←ranks281_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0035.r281.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a281.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0035.ordered281_checked hr ha ho
theorem frozen_frame281 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281 ReferenceProfileData.CoarseLowerShape.Batch0035.r281.bounds ReferenceProfileData.CoarseLowerShape.Batch0035.a281.bounds
  · rw [←r_profile281_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile281_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry281_linked.2.2.2.2.1
  · exact geometry281_linked.2.2.2.2.2
  · exact r_reference281_checked
  · exact a_reference281_checked
  · exact r_fixed281_linked
  · exact a_fixed281_linked
  · exact time281_checked
  · exact ht
  · exact hw
theorem child_geometry281_checked : ReferenceWeightData.CoarseLowerShape.Batch0070.cert562.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0070.cert562.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0070.cert563.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0070.cert563.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights281 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0070.cert562∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch70_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0070.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0070.cert563∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch70_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0070.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0070.cert562.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0070.cert562.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0070.cert562.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry281_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights562_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0070.cert563.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0070.cert563.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry281_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry281_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights563_linked j (List.mem_finRange j))
theorem actual_frozen_frame281 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame281 (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.flow.timeParameter_mem child_geometry281_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights281 hz)
theorem r_profile282_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.r282=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0035.r282.bounds := by rfl
theorem a_profile282_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.a282=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0035.a282.bounds := by rfl
theorem r_fixed282_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.r282.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r282.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r282.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r282.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed 7 := by decide +kernel
theorem a_fixed282_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.a282.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.a282.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed 9 := by decide +kernel
theorem ranks282_linked : ReferenceRankData.CoarseLowerShape.Batch0035.targetR282=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0035.targetA282=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed 1 := by decide +kernel
theorem r_input282_linked : ReferenceRankData.CoarseLowerShape.Batch0035.r282.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0035.r282.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0035.r282.bounds.gauge] := by decide +kernel
theorem a_input282_linked : ReferenceRankData.CoarseLowerShape.Batch0035.a282.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0035.a282.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0035.a282.bounds.gauge] := by decide +kernel
theorem geometry282_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.right.a := by decide +kernel
theorem weights564_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0070.cert564.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights565_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0070.cert565.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time282_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed 10)=true := by decide +kernel
theorem r_reference282_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed 0)=true := by decide +kernel
theorem a_reference282_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed 1)=true := by decide +kernel
theorem rank_r_link282_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0035.r282.bounds ReferenceRankData.CoarseLowerShape.Batch0035.r282 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link282_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0035.a282.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a282 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints282 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell true ReferenceProfileData.CoarseLowerShape.Batch0035.r282.bounds ReferenceRankData.CoarseLowerShape.Batch0035.r282 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile282_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0035.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0035.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link282_checked
    geometry282_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell false ReferenceProfileData.CoarseLowerShape.Batch0035.a282.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a282 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile282_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0035.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0035.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link282_checked
    geometry282_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks282_linked.1,←ranks282_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0035.r282.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a282.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0035.ordered282_checked hr ha ho
theorem frozen_frame282 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282 ReferenceProfileData.CoarseLowerShape.Batch0035.r282.bounds ReferenceProfileData.CoarseLowerShape.Batch0035.a282.bounds
  · rw [←r_profile282_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile282_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry282_linked.2.2.2.2.1
  · exact geometry282_linked.2.2.2.2.2
  · exact r_reference282_checked
  · exact a_reference282_checked
  · exact r_fixed282_linked
  · exact a_fixed282_linked
  · exact time282_checked
  · exact ht
  · exact hw
theorem child_geometry282_checked : ReferenceWeightData.CoarseLowerShape.Batch0070.cert564.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0070.cert564.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0070.cert565.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0070.cert565.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights282 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0070.cert564∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch70_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0070.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0070.cert565∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch70_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0070.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0070.cert564.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0070.cert564.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0070.cert564.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry282_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights564_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0070.cert565.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0070.cert565.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry282_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry282_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights565_linked j (List.mem_finRange j))
theorem actual_frozen_frame282 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame282 (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.flow.timeParameter_mem child_geometry282_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights282 hz)
theorem r_profile283_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.r283=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0035.r283.bounds := by rfl
theorem a_profile283_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.a283=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0035.a283.bounds := by rfl
theorem r_fixed283_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.r283.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r283.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r283.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r283.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed 7 := by decide +kernel
theorem a_fixed283_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.a283.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.a283.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed 9 := by decide +kernel
theorem ranks283_linked : ReferenceRankData.CoarseLowerShape.Batch0035.targetR283=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0035.targetA283=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed 1 := by decide +kernel
theorem r_input283_linked : ReferenceRankData.CoarseLowerShape.Batch0035.r283.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0035.r283.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0035.r283.bounds.gauge] := by decide +kernel
theorem a_input283_linked : ReferenceRankData.CoarseLowerShape.Batch0035.a283.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0035.a283.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0035.a283.bounds.gauge] := by decide +kernel
theorem geometry283_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.right.a := by decide +kernel
theorem weights566_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0070.cert566.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights567_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0070.cert567.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time283_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed 10)=true := by decide +kernel
theorem r_reference283_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed 0)=true := by decide +kernel
theorem a_reference283_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed 1)=true := by decide +kernel
theorem rank_r_link283_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0035.r283.bounds ReferenceRankData.CoarseLowerShape.Batch0035.r283 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link283_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0035.a283.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a283 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints283 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell true ReferenceProfileData.CoarseLowerShape.Batch0035.r283.bounds ReferenceRankData.CoarseLowerShape.Batch0035.r283 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile283_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0035.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0035.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link283_checked
    geometry283_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell false ReferenceProfileData.CoarseLowerShape.Batch0035.a283.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a283 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile283_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0035.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0035.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link283_checked
    geometry283_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks283_linked.1,←ranks283_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0035.r283.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a283.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0035.ordered283_checked hr ha ho
theorem frozen_frame283 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283 ReferenceProfileData.CoarseLowerShape.Batch0035.r283.bounds ReferenceProfileData.CoarseLowerShape.Batch0035.a283.bounds
  · rw [←r_profile283_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile283_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry283_linked.2.2.2.2.1
  · exact geometry283_linked.2.2.2.2.2
  · exact r_reference283_checked
  · exact a_reference283_checked
  · exact r_fixed283_linked
  · exact a_fixed283_linked
  · exact time283_checked
  · exact ht
  · exact hw
theorem child_geometry283_checked : ReferenceWeightData.CoarseLowerShape.Batch0070.cert566.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0070.cert566.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0070.cert567.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0070.cert567.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights283 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0070.cert566∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch70_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0070.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0070.cert567∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch70_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0070.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0070.cert566.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0070.cert566.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0070.cert566.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry283_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights566_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0070.cert567.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0070.cert567.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry283_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry283_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights567_linked j (List.mem_finRange j))
theorem actual_frozen_frame283 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame283 (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.flow.timeParameter_mem child_geometry283_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights283 hz)
theorem r_profile284_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.r284=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0035.r284.bounds := by rfl
theorem a_profile284_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.a284=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0035.a284.bounds := by rfl
theorem r_fixed284_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.r284.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r284.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r284.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r284.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed 7 := by decide +kernel
theorem a_fixed284_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.a284.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.a284.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed 9 := by decide +kernel
theorem ranks284_linked : ReferenceRankData.CoarseLowerShape.Batch0035.targetR284=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0035.targetA284=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed 1 := by decide +kernel
theorem r_input284_linked : ReferenceRankData.CoarseLowerShape.Batch0035.r284.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0035.r284.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0035.r284.bounds.gauge] := by decide +kernel
theorem a_input284_linked : ReferenceRankData.CoarseLowerShape.Batch0035.a284.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0035.a284.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0035.a284.bounds.gauge] := by decide +kernel
theorem geometry284_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.right.a := by decide +kernel
theorem weights568_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0071.cert568.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights569_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0071.cert569.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time284_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed 10)=true := by decide +kernel
theorem r_reference284_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed 0)=true := by decide +kernel
theorem a_reference284_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed 1)=true := by decide +kernel
theorem rank_r_link284_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0035.r284.bounds ReferenceRankData.CoarseLowerShape.Batch0035.r284 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link284_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0035.a284.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a284 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints284 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell true ReferenceProfileData.CoarseLowerShape.Batch0035.r284.bounds ReferenceRankData.CoarseLowerShape.Batch0035.r284 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile284_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0035.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0035.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link284_checked
    geometry284_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell false ReferenceProfileData.CoarseLowerShape.Batch0035.a284.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a284 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile284_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0035.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0035.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link284_checked
    geometry284_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks284_linked.1,←ranks284_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0035.r284.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a284.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0035.ordered284_checked hr ha ho
theorem frozen_frame284 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284 ReferenceProfileData.CoarseLowerShape.Batch0035.r284.bounds ReferenceProfileData.CoarseLowerShape.Batch0035.a284.bounds
  · rw [←r_profile284_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile284_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry284_linked.2.2.2.2.1
  · exact geometry284_linked.2.2.2.2.2
  · exact r_reference284_checked
  · exact a_reference284_checked
  · exact r_fixed284_linked
  · exact a_fixed284_linked
  · exact time284_checked
  · exact ht
  · exact hw
theorem child_geometry284_checked : ReferenceWeightData.CoarseLowerShape.Batch0071.cert568.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0071.cert568.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0071.cert569.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0071.cert569.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights284 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0071.cert568∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch71_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0071.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0071.cert569∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch71_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0071.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0071.cert568.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0071.cert568.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0071.cert568.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry284_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights568_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0071.cert569.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0071.cert569.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry284_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry284_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights569_linked j (List.mem_finRange j))
theorem actual_frozen_frame284 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame284 (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.flow.timeParameter_mem child_geometry284_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights284 hz)
theorem r_profile285_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.r285=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0035.r285.bounds := by rfl
theorem a_profile285_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.a285=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0035.a285.bounds := by rfl
theorem r_fixed285_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.r285.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r285.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r285.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r285.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed 7 := by decide +kernel
theorem a_fixed285_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.a285.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.a285.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed 9 := by decide +kernel
theorem ranks285_linked : ReferenceRankData.CoarseLowerShape.Batch0035.targetR285=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0035.targetA285=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed 1 := by decide +kernel
theorem r_input285_linked : ReferenceRankData.CoarseLowerShape.Batch0035.r285.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0035.r285.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0035.r285.bounds.gauge] := by decide +kernel
theorem a_input285_linked : ReferenceRankData.CoarseLowerShape.Batch0035.a285.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0035.a285.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0035.a285.bounds.gauge] := by decide +kernel
theorem geometry285_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.right.a := by decide +kernel
theorem weights570_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0071.cert570.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights571_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0071.cert571.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time285_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed 10)=true := by decide +kernel
theorem r_reference285_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed 0)=true := by decide +kernel
theorem a_reference285_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed 1)=true := by decide +kernel
theorem rank_r_link285_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0035.r285.bounds ReferenceRankData.CoarseLowerShape.Batch0035.r285 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link285_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0035.a285.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a285 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints285 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell true ReferenceProfileData.CoarseLowerShape.Batch0035.r285.bounds ReferenceRankData.CoarseLowerShape.Batch0035.r285 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile285_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0035.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0035.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link285_checked
    geometry285_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell false ReferenceProfileData.CoarseLowerShape.Batch0035.a285.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a285 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile285_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0035.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0035.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link285_checked
    geometry285_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks285_linked.1,←ranks285_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0035.r285.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a285.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0035.ordered285_checked hr ha ho
theorem frozen_frame285 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285 ReferenceProfileData.CoarseLowerShape.Batch0035.r285.bounds ReferenceProfileData.CoarseLowerShape.Batch0035.a285.bounds
  · rw [←r_profile285_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile285_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry285_linked.2.2.2.2.1
  · exact geometry285_linked.2.2.2.2.2
  · exact r_reference285_checked
  · exact a_reference285_checked
  · exact r_fixed285_linked
  · exact a_fixed285_linked
  · exact time285_checked
  · exact ht
  · exact hw
theorem child_geometry285_checked : ReferenceWeightData.CoarseLowerShape.Batch0071.cert570.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0071.cert570.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0071.cert571.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0071.cert571.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights285 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0071.cert570∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch71_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0071.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0071.cert571∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch71_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0071.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0071.cert570.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0071.cert570.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0071.cert570.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry285_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights570_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0071.cert571.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0071.cert571.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry285_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry285_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights571_linked j (List.mem_finRange j))
theorem actual_frozen_frame285 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame285 (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.flow.timeParameter_mem child_geometry285_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights285 hz)
theorem r_profile286_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.r286=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0035.r286.bounds := by rfl
theorem a_profile286_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.a286=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0035.a286.bounds := by rfl
theorem r_fixed286_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.r286.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r286.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r286.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r286.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed 7 := by decide +kernel
theorem a_fixed286_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.a286.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.a286.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed 9 := by decide +kernel
theorem ranks286_linked : ReferenceRankData.CoarseLowerShape.Batch0035.targetR286=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0035.targetA286=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed 1 := by decide +kernel
theorem r_input286_linked : ReferenceRankData.CoarseLowerShape.Batch0035.r286.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0035.r286.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0035.r286.bounds.gauge] := by decide +kernel
theorem a_input286_linked : ReferenceRankData.CoarseLowerShape.Batch0035.a286.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0035.a286.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0035.a286.bounds.gauge] := by decide +kernel
theorem geometry286_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.right.a := by decide +kernel
theorem weights572_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0071.cert572.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights573_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0071.cert573.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time286_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed 10)=true := by decide +kernel
theorem r_reference286_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed 0)=true := by decide +kernel
theorem a_reference286_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed 1)=true := by decide +kernel
theorem rank_r_link286_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0035.r286.bounds ReferenceRankData.CoarseLowerShape.Batch0035.r286 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link286_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0035.a286.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a286 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints286 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell true ReferenceProfileData.CoarseLowerShape.Batch0035.r286.bounds ReferenceRankData.CoarseLowerShape.Batch0035.r286 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile286_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0035.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0035.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link286_checked
    geometry286_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell false ReferenceProfileData.CoarseLowerShape.Batch0035.a286.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a286 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile286_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0035.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0035.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link286_checked
    geometry286_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks286_linked.1,←ranks286_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0035.r286.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a286.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0035.ordered286_checked hr ha ho
theorem frozen_frame286 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286 ReferenceProfileData.CoarseLowerShape.Batch0035.r286.bounds ReferenceProfileData.CoarseLowerShape.Batch0035.a286.bounds
  · rw [←r_profile286_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile286_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry286_linked.2.2.2.2.1
  · exact geometry286_linked.2.2.2.2.2
  · exact r_reference286_checked
  · exact a_reference286_checked
  · exact r_fixed286_linked
  · exact a_fixed286_linked
  · exact time286_checked
  · exact ht
  · exact hw
theorem child_geometry286_checked : ReferenceWeightData.CoarseLowerShape.Batch0071.cert572.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0071.cert572.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0071.cert573.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0071.cert573.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights286 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0071.cert572∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch71_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0071.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0071.cert573∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch71_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0071.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0071.cert572.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0071.cert572.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0071.cert572.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry286_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights572_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0071.cert573.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0071.cert573.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry286_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry286_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights573_linked j (List.mem_finRange j))
theorem actual_frozen_frame286 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame286 (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.flow.timeParameter_mem child_geometry286_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights286 hz)
theorem r_profile287_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.r287=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0035.r287.bounds := by rfl
theorem a_profile287_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.a287=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0035.a287.bounds := by rfl
theorem r_fixed287_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.r287.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r287.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r287.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.r287.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed 7 := by decide +kernel
theorem a_fixed287_linked : ReferenceProfileData.CoarseLowerShape.Batch0035.a287.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0035.a287.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed 9 := by decide +kernel
theorem ranks287_linked : ReferenceRankData.CoarseLowerShape.Batch0035.targetR287=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0035.targetA287=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed 1 := by decide +kernel
theorem r_input287_linked : ReferenceRankData.CoarseLowerShape.Batch0035.r287.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0035.r287.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0035.r287.bounds.gauge] := by decide +kernel
theorem a_input287_linked : ReferenceRankData.CoarseLowerShape.Batch0035.a287.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0035.a287.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0035.a287.bounds.gauge] := by decide +kernel
theorem geometry287_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.right.a := by decide +kernel
theorem weights574_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0071.cert574.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights575_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0071.cert575.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time287_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed 10)=true := by decide +kernel
theorem r_reference287_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed 0)=true := by decide +kernel
theorem a_reference287_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed 1)=true := by decide +kernel
theorem rank_r_link287_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0035.r287.bounds ReferenceRankData.CoarseLowerShape.Batch0035.r287 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link287_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0035.a287.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a287 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints287 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell true ReferenceProfileData.CoarseLowerShape.Batch0035.r287.bounds ReferenceRankData.CoarseLowerShape.Batch0035.r287 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile287_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0035.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0035.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link287_checked
    geometry287_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell false ReferenceProfileData.CoarseLowerShape.Batch0035.a287.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a287 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile287_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0035.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0035.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link287_checked
    geometry287_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks287_linked.1,←ranks287_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0035.r287.bounds ReferenceRankData.CoarseLowerShape.Batch0035.a287.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0035.ordered287_checked hr ha ho
theorem frozen_frame287 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287 ReferenceProfileData.CoarseLowerShape.Batch0035.r287.bounds ReferenceProfileData.CoarseLowerShape.Batch0035.a287.bounds
  · rw [←r_profile287_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile287_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry287_linked.2.2.2.2.1
  · exact geometry287_linked.2.2.2.2.2
  · exact r_reference287_checked
  · exact a_reference287_checked
  · exact r_fixed287_linked
  · exact a_fixed287_linked
  · exact time287_checked
  · exact ht
  · exact hw
theorem child_geometry287_checked : ReferenceWeightData.CoarseLowerShape.Batch0071.cert574.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0071.cert574.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0071.cert575.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0071.cert575.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights287 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0071.cert574∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch71_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0071.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0071.cert575∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch71_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0071.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0071.cert574.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0071.cert574.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0071.cert574.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry287_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights574_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0071.cert575.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0071.cert575.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry287_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry287_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights575_linked j (List.mem_finRange j))
theorem actual_frozen_frame287 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame287 (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.flow.timeParameter_mem child_geometry287_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights287 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell280),(ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell281),(ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell282),(ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell283),(ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell284),(ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell285),(ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell286),(ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0035.cell287)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0035.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0035.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame280 hz
  · exact fun z hz=>actual_frozen_frame281 hz
  · exact fun z hz=>actual_frozen_frame282 hz
  · exact fun z hz=>actual_frozen_frame283 hz
  · exact fun z hz=>actual_frozen_frame284 hz
  · exact fun z hz=>actual_frozen_frame285 hz
  · exact fun z hz=>actual_frozen_frame286 hz
  · exact fun z hz=>actual_frozen_frame287 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints280 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints281 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints282 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints283 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints284 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints285 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints286 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints287 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry280_linked.1,geometry280_linked.2.1,geometry280_linked.2.2.1,geometry280_linked.2.2.2.1⟩
  · exact ⟨geometry281_linked.1,geometry281_linked.2.1,geometry281_linked.2.2.1,geometry281_linked.2.2.2.1⟩
  · exact ⟨geometry282_linked.1,geometry282_linked.2.1,geometry282_linked.2.2.1,geometry282_linked.2.2.2.1⟩
  · exact ⟨geometry283_linked.1,geometry283_linked.2.1,geometry283_linked.2.2.1,geometry283_linked.2.2.2.1⟩
  · exact ⟨geometry284_linked.1,geometry284_linked.2.1,geometry284_linked.2.2.1,geometry284_linked.2.2.2.1⟩
  · exact ⟨geometry285_linked.1,geometry285_linked.2.1,geometry285_linked.2.2.1,geometry285_linked.2.2.2.1⟩
  · exact ⟨geometry286_linked.1,geometry286_linked.2.1,geometry286_linked.2.2.1,geometry286_linked.2.2.2.1⟩
  · exact ⟨geometry287_linked.1,geometry287_linked.2.1,geometry287_linked.2.2.1,geometry287_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0035.a280.bounds,?_,geometry280_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0035.a280.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile280_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0035.r280.bounds,?_,geometry280_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert280.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0035.r280.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile280_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0035.a281.bounds,?_,geometry281_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0035.a281.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile281_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0035.r281.bounds,?_,geometry281_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert281.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0035.r281.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile281_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0035.a282.bounds,?_,geometry282_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0035.a282.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile282_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0035.r282.bounds,?_,geometry282_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert282.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0035.r282.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile282_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0035.a283.bounds,?_,geometry283_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0035.a283.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile283_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0035.r283.bounds,?_,geometry283_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert283.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0035.r283.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile283_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0035.a284.bounds,?_,geometry284_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0035.a284.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile284_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0035.r284.bounds,?_,geometry284_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert284.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0035.r284.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile284_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0035.a285.bounds,?_,geometry285_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0035.a285.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile285_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0035.r285.bounds,?_,geometry285_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert285.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0035.r285.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile285_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0035.a286.bounds,?_,geometry286_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0035.a286.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile286_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0035.r286.bounds,?_,geometry286_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert286.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0035.r286.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile286_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0035.a287.bounds,?_,geometry287_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0035.a287.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile287_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0035.r287.bounds,?_,geometry287_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0035.cert287.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0035.r287.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile287_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0035.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0035.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0035
