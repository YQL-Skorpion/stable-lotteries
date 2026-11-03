import OptimalG.Certificates.ReferenceSupportGeometry
import OptimalG.Certificates.ReferenceMatchedFrame
import OptimalG.Certificates.ReferenceBranchGeometry
import OptimalG.Certificates.ReferenceTimeBounds
import OptimalG.Certificates.ReferenceFrozenProfiles
import OptimalG.Certificates.ReferenceHessianFrame
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0005_0008
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0005_0008
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0013_0016
import OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Batch0007
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0007_0010
import OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0006
namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch14_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0014.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0014.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch15_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0015.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0015.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile56_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.r56=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0007.r56.bounds := by rfl
theorem a_profile56_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.a56=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0007.a56.bounds := by rfl
theorem r_fixed56_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.r56.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r56.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r56.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r56.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed 7 := by decide +kernel
theorem a_fixed56_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.a56.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.a56.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed 9 := by decide +kernel
theorem ranks56_linked : ReferenceRankData.CoarseLowerShape.Batch0007.targetR56=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0007.targetA56=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed 1 := by decide +kernel
theorem r_input56_linked : ReferenceRankData.CoarseLowerShape.Batch0007.r56.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0007.r56.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0007.r56.bounds.gauge] := by decide +kernel
theorem a_input56_linked : ReferenceRankData.CoarseLowerShape.Batch0007.a56.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0007.a56.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0007.a56.bounds.gauge] := by decide +kernel
theorem geometry56_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.right.a := by decide +kernel
theorem weights112_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0014.cert112.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights113_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0014.cert113.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time56_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed 10)=true := by decide +kernel
theorem r_reference56_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed 0)=true := by decide +kernel
theorem a_reference56_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed 1)=true := by decide +kernel
theorem rank_r_link56_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0007.r56.bounds ReferenceRankData.CoarseLowerShape.Batch0007.r56 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link56_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0007.a56.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a56 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints56 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell true ReferenceProfileData.CoarseLowerShape.Batch0007.r56.bounds ReferenceRankData.CoarseLowerShape.Batch0007.r56 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile56_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0007.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0007.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link56_checked
    geometry56_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell false ReferenceProfileData.CoarseLowerShape.Batch0007.a56.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a56 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile56_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0007.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0007.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link56_checked
    geometry56_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks56_linked.1,←ranks56_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0007.r56.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a56.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0007.ordered56_checked hr ha ho
theorem frozen_frame56 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56 ReferenceProfileData.CoarseLowerShape.Batch0007.r56.bounds ReferenceProfileData.CoarseLowerShape.Batch0007.a56.bounds
  · rw [←r_profile56_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile56_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry56_linked.2.2.2.2.1
  · exact geometry56_linked.2.2.2.2.2
  · exact r_reference56_checked
  · exact a_reference56_checked
  · exact r_fixed56_linked
  · exact a_fixed56_linked
  · exact time56_checked
  · exact ht
  · exact hw
theorem child_geometry56_checked : ReferenceWeightData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights56 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0014.cert112∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch14_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0014.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0014.cert113∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch14_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0014.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry56_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights112_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry56_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry56_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights113_linked j (List.mem_finRange j))
theorem actual_frozen_frame56 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame56 (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.flow.timeParameter_mem child_geometry56_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights56 hz)
theorem r_profile57_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.r57=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0007.r57.bounds := by rfl
theorem a_profile57_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.a57=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0007.a57.bounds := by rfl
theorem r_fixed57_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.r57.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r57.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r57.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r57.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed 7 := by decide +kernel
theorem a_fixed57_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.a57.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.a57.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed 9 := by decide +kernel
theorem ranks57_linked : ReferenceRankData.CoarseLowerShape.Batch0007.targetR57=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0007.targetA57=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed 1 := by decide +kernel
theorem r_input57_linked : ReferenceRankData.CoarseLowerShape.Batch0007.r57.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0007.r57.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0007.r57.bounds.gauge] := by decide +kernel
theorem a_input57_linked : ReferenceRankData.CoarseLowerShape.Batch0007.a57.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0007.a57.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0007.a57.bounds.gauge] := by decide +kernel
theorem geometry57_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.right.a := by decide +kernel
theorem weights114_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0014.cert114.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights115_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0014.cert115.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time57_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed 10)=true := by decide +kernel
theorem r_reference57_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed 0)=true := by decide +kernel
theorem a_reference57_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed 1)=true := by decide +kernel
theorem rank_r_link57_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0007.r57.bounds ReferenceRankData.CoarseLowerShape.Batch0007.r57 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link57_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0007.a57.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a57 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints57 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell true ReferenceProfileData.CoarseLowerShape.Batch0007.r57.bounds ReferenceRankData.CoarseLowerShape.Batch0007.r57 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile57_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0007.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0007.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link57_checked
    geometry57_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell false ReferenceProfileData.CoarseLowerShape.Batch0007.a57.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a57 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile57_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0007.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0007.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link57_checked
    geometry57_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks57_linked.1,←ranks57_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0007.r57.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a57.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0007.ordered57_checked hr ha ho
theorem frozen_frame57 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57 ReferenceProfileData.CoarseLowerShape.Batch0007.r57.bounds ReferenceProfileData.CoarseLowerShape.Batch0007.a57.bounds
  · rw [←r_profile57_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile57_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry57_linked.2.2.2.2.1
  · exact geometry57_linked.2.2.2.2.2
  · exact r_reference57_checked
  · exact a_reference57_checked
  · exact r_fixed57_linked
  · exact a_fixed57_linked
  · exact time57_checked
  · exact ht
  · exact hw
theorem child_geometry57_checked : ReferenceWeightData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights57 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0014.cert114∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch14_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0014.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0014.cert115∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch14_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0014.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry57_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights114_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry57_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry57_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights115_linked j (List.mem_finRange j))
theorem actual_frozen_frame57 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame57 (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.flow.timeParameter_mem child_geometry57_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights57 hz)
theorem r_profile58_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.r58=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0007.r58.bounds := by rfl
theorem a_profile58_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.a58=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0007.a58.bounds := by rfl
theorem r_fixed58_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.r58.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r58.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r58.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r58.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed 7 := by decide +kernel
theorem a_fixed58_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.a58.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.a58.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed 9 := by decide +kernel
theorem ranks58_linked : ReferenceRankData.CoarseLowerShape.Batch0007.targetR58=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0007.targetA58=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed 1 := by decide +kernel
theorem r_input58_linked : ReferenceRankData.CoarseLowerShape.Batch0007.r58.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0007.r58.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0007.r58.bounds.gauge] := by decide +kernel
theorem a_input58_linked : ReferenceRankData.CoarseLowerShape.Batch0007.a58.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0007.a58.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0007.a58.bounds.gauge] := by decide +kernel
theorem geometry58_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.right.a := by decide +kernel
theorem weights116_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0014.cert116.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights117_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0014.cert117.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time58_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed 10)=true := by decide +kernel
theorem r_reference58_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed 0)=true := by decide +kernel
theorem a_reference58_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed 1)=true := by decide +kernel
theorem rank_r_link58_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0007.r58.bounds ReferenceRankData.CoarseLowerShape.Batch0007.r58 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link58_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0007.a58.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a58 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints58 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell true ReferenceProfileData.CoarseLowerShape.Batch0007.r58.bounds ReferenceRankData.CoarseLowerShape.Batch0007.r58 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile58_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0007.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0007.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link58_checked
    geometry58_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell false ReferenceProfileData.CoarseLowerShape.Batch0007.a58.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a58 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile58_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0007.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0007.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link58_checked
    geometry58_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks58_linked.1,←ranks58_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0007.r58.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a58.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0007.ordered58_checked hr ha ho
theorem frozen_frame58 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58 ReferenceProfileData.CoarseLowerShape.Batch0007.r58.bounds ReferenceProfileData.CoarseLowerShape.Batch0007.a58.bounds
  · rw [←r_profile58_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile58_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry58_linked.2.2.2.2.1
  · exact geometry58_linked.2.2.2.2.2
  · exact r_reference58_checked
  · exact a_reference58_checked
  · exact r_fixed58_linked
  · exact a_fixed58_linked
  · exact time58_checked
  · exact ht
  · exact hw
theorem child_geometry58_checked : ReferenceWeightData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights58 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0014.cert116∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch14_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0014.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0014.cert117∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch14_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0014.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry58_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights116_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry58_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry58_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights117_linked j (List.mem_finRange j))
theorem actual_frozen_frame58 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame58 (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.flow.timeParameter_mem child_geometry58_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights58 hz)
theorem r_profile59_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.r59=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0007.r59.bounds := by rfl
theorem a_profile59_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.a59=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0007.a59.bounds := by rfl
theorem r_fixed59_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.r59.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r59.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r59.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r59.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed 7 := by decide +kernel
theorem a_fixed59_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.a59.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.a59.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed 9 := by decide +kernel
theorem ranks59_linked : ReferenceRankData.CoarseLowerShape.Batch0007.targetR59=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0007.targetA59=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed 1 := by decide +kernel
theorem r_input59_linked : ReferenceRankData.CoarseLowerShape.Batch0007.r59.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0007.r59.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0007.r59.bounds.gauge] := by decide +kernel
theorem a_input59_linked : ReferenceRankData.CoarseLowerShape.Batch0007.a59.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0007.a59.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0007.a59.bounds.gauge] := by decide +kernel
theorem geometry59_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.right.a := by decide +kernel
theorem weights118_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0014.cert118.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights119_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0014.cert119.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time59_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed 10)=true := by decide +kernel
theorem r_reference59_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed 0)=true := by decide +kernel
theorem a_reference59_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed 1)=true := by decide +kernel
theorem rank_r_link59_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0007.r59.bounds ReferenceRankData.CoarseLowerShape.Batch0007.r59 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link59_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0007.a59.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a59 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints59 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell true ReferenceProfileData.CoarseLowerShape.Batch0007.r59.bounds ReferenceRankData.CoarseLowerShape.Batch0007.r59 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile59_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0007.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0007.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link59_checked
    geometry59_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell false ReferenceProfileData.CoarseLowerShape.Batch0007.a59.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a59 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile59_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0007.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0007.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link59_checked
    geometry59_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks59_linked.1,←ranks59_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0007.r59.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a59.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0007.ordered59_checked hr ha ho
theorem frozen_frame59 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59 ReferenceProfileData.CoarseLowerShape.Batch0007.r59.bounds ReferenceProfileData.CoarseLowerShape.Batch0007.a59.bounds
  · rw [←r_profile59_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile59_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry59_linked.2.2.2.2.1
  · exact geometry59_linked.2.2.2.2.2
  · exact r_reference59_checked
  · exact a_reference59_checked
  · exact r_fixed59_linked
  · exact a_fixed59_linked
  · exact time59_checked
  · exact ht
  · exact hw
theorem child_geometry59_checked : ReferenceWeightData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights59 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0014.cert118∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch14_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0014.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0014.cert119∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch14_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0014.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry59_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights118_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry59_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry59_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights119_linked j (List.mem_finRange j))
theorem actual_frozen_frame59 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame59 (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.flow.timeParameter_mem child_geometry59_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights59 hz)
theorem r_profile60_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.r60=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0007.r60.bounds := by rfl
theorem a_profile60_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.a60=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0007.a60.bounds := by rfl
theorem r_fixed60_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.r60.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r60.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r60.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r60.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed 7 := by decide +kernel
theorem a_fixed60_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.a60.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.a60.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed 9 := by decide +kernel
theorem ranks60_linked : ReferenceRankData.CoarseLowerShape.Batch0007.targetR60=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0007.targetA60=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed 1 := by decide +kernel
theorem r_input60_linked : ReferenceRankData.CoarseLowerShape.Batch0007.r60.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0007.r60.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0007.r60.bounds.gauge] := by decide +kernel
theorem a_input60_linked : ReferenceRankData.CoarseLowerShape.Batch0007.a60.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0007.a60.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0007.a60.bounds.gauge] := by decide +kernel
theorem geometry60_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.right.a := by decide +kernel
theorem weights120_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0015.cert120.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights121_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0015.cert121.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time60_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed 10)=true := by decide +kernel
theorem r_reference60_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed 0)=true := by decide +kernel
theorem a_reference60_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed 1)=true := by decide +kernel
theorem rank_r_link60_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0007.r60.bounds ReferenceRankData.CoarseLowerShape.Batch0007.r60 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link60_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0007.a60.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a60 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints60 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell true ReferenceProfileData.CoarseLowerShape.Batch0007.r60.bounds ReferenceRankData.CoarseLowerShape.Batch0007.r60 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile60_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0007.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0007.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link60_checked
    geometry60_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell false ReferenceProfileData.CoarseLowerShape.Batch0007.a60.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a60 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile60_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0007.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0007.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link60_checked
    geometry60_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks60_linked.1,←ranks60_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0007.r60.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a60.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0007.ordered60_checked hr ha ho
theorem frozen_frame60 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60 ReferenceProfileData.CoarseLowerShape.Batch0007.r60.bounds ReferenceProfileData.CoarseLowerShape.Batch0007.a60.bounds
  · rw [←r_profile60_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile60_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry60_linked.2.2.2.2.1
  · exact geometry60_linked.2.2.2.2.2
  · exact r_reference60_checked
  · exact a_reference60_checked
  · exact r_fixed60_linked
  · exact a_fixed60_linked
  · exact time60_checked
  · exact ht
  · exact hw
theorem child_geometry60_checked : ReferenceWeightData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights60 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0015.cert120∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch15_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0015.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0015.cert121∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch15_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0015.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry60_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights120_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry60_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry60_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights121_linked j (List.mem_finRange j))
theorem actual_frozen_frame60 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame60 (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.flow.timeParameter_mem child_geometry60_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights60 hz)
theorem r_profile61_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.r61=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0007.r61.bounds := by rfl
theorem a_profile61_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.a61=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0007.a61.bounds := by rfl
theorem r_fixed61_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.r61.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r61.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r61.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r61.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed 7 := by decide +kernel
theorem a_fixed61_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.a61.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.a61.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed 9 := by decide +kernel
theorem ranks61_linked : ReferenceRankData.CoarseLowerShape.Batch0007.targetR61=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0007.targetA61=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed 1 := by decide +kernel
theorem r_input61_linked : ReferenceRankData.CoarseLowerShape.Batch0007.r61.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0007.r61.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0007.r61.bounds.gauge] := by decide +kernel
theorem a_input61_linked : ReferenceRankData.CoarseLowerShape.Batch0007.a61.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0007.a61.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0007.a61.bounds.gauge] := by decide +kernel
theorem geometry61_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.right.a := by decide +kernel
theorem weights122_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0015.cert122.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights123_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0015.cert123.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time61_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed 10)=true := by decide +kernel
theorem r_reference61_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed 0)=true := by decide +kernel
theorem a_reference61_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed 1)=true := by decide +kernel
theorem rank_r_link61_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0007.r61.bounds ReferenceRankData.CoarseLowerShape.Batch0007.r61 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link61_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0007.a61.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a61 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints61 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell true ReferenceProfileData.CoarseLowerShape.Batch0007.r61.bounds ReferenceRankData.CoarseLowerShape.Batch0007.r61 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile61_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0007.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0007.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link61_checked
    geometry61_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell false ReferenceProfileData.CoarseLowerShape.Batch0007.a61.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a61 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile61_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0007.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0007.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link61_checked
    geometry61_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks61_linked.1,←ranks61_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0007.r61.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a61.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0007.ordered61_checked hr ha ho
theorem frozen_frame61 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61 ReferenceProfileData.CoarseLowerShape.Batch0007.r61.bounds ReferenceProfileData.CoarseLowerShape.Batch0007.a61.bounds
  · rw [←r_profile61_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile61_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry61_linked.2.2.2.2.1
  · exact geometry61_linked.2.2.2.2.2
  · exact r_reference61_checked
  · exact a_reference61_checked
  · exact r_fixed61_linked
  · exact a_fixed61_linked
  · exact time61_checked
  · exact ht
  · exact hw
theorem child_geometry61_checked : ReferenceWeightData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights61 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0015.cert122∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch15_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0015.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0015.cert123∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch15_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0015.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry61_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights122_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry61_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry61_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights123_linked j (List.mem_finRange j))
theorem actual_frozen_frame61 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame61 (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.flow.timeParameter_mem child_geometry61_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights61 hz)
theorem r_profile62_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.r62=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0007.r62.bounds := by rfl
theorem a_profile62_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.a62=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0007.a62.bounds := by rfl
theorem r_fixed62_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.r62.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r62.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r62.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r62.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed 7 := by decide +kernel
theorem a_fixed62_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.a62.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.a62.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed 9 := by decide +kernel
theorem ranks62_linked : ReferenceRankData.CoarseLowerShape.Batch0007.targetR62=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0007.targetA62=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed 1 := by decide +kernel
theorem r_input62_linked : ReferenceRankData.CoarseLowerShape.Batch0007.r62.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0007.r62.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0007.r62.bounds.gauge] := by decide +kernel
theorem a_input62_linked : ReferenceRankData.CoarseLowerShape.Batch0007.a62.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0007.a62.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0007.a62.bounds.gauge] := by decide +kernel
theorem geometry62_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.right.a := by decide +kernel
theorem weights124_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0015.cert124.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights125_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0015.cert125.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time62_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed 10)=true := by decide +kernel
theorem r_reference62_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed 0)=true := by decide +kernel
theorem a_reference62_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed 1)=true := by decide +kernel
theorem rank_r_link62_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0007.r62.bounds ReferenceRankData.CoarseLowerShape.Batch0007.r62 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link62_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0007.a62.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a62 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints62 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell true ReferenceProfileData.CoarseLowerShape.Batch0007.r62.bounds ReferenceRankData.CoarseLowerShape.Batch0007.r62 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile62_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0007.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0007.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link62_checked
    geometry62_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell false ReferenceProfileData.CoarseLowerShape.Batch0007.a62.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a62 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile62_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0007.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0007.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link62_checked
    geometry62_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks62_linked.1,←ranks62_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0007.r62.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a62.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0007.ordered62_checked hr ha ho
theorem frozen_frame62 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62 ReferenceProfileData.CoarseLowerShape.Batch0007.r62.bounds ReferenceProfileData.CoarseLowerShape.Batch0007.a62.bounds
  · rw [←r_profile62_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile62_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry62_linked.2.2.2.2.1
  · exact geometry62_linked.2.2.2.2.2
  · exact r_reference62_checked
  · exact a_reference62_checked
  · exact r_fixed62_linked
  · exact a_fixed62_linked
  · exact time62_checked
  · exact ht
  · exact hw
theorem child_geometry62_checked : ReferenceWeightData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights62 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0015.cert124∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch15_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0015.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0015.cert125∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch15_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0015.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry62_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights124_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry62_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry62_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights125_linked j (List.mem_finRange j))
theorem actual_frozen_frame62 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame62 (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.flow.timeParameter_mem child_geometry62_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights62 hz)
theorem r_profile63_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.r63=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0007.r63.bounds := by rfl
theorem a_profile63_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.a63=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0007.a63.bounds := by rfl
theorem r_fixed63_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.r63.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r63.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r63.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.r63.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed 7 := by decide +kernel
theorem a_fixed63_linked : ReferenceProfileData.CoarseLowerShape.Batch0007.a63.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0007.a63.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed 9 := by decide +kernel
theorem ranks63_linked : ReferenceRankData.CoarseLowerShape.Batch0007.targetR63=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0007.targetA63=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed 1 := by decide +kernel
theorem r_input63_linked : ReferenceRankData.CoarseLowerShape.Batch0007.r63.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0007.r63.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0007.r63.bounds.gauge] := by decide +kernel
theorem a_input63_linked : ReferenceRankData.CoarseLowerShape.Batch0007.a63.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0007.a63.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0007.a63.bounds.gauge] := by decide +kernel
theorem geometry63_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.right.a := by decide +kernel
theorem weights126_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0015.cert126.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights127_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0015.cert127.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time63_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed 10)=true := by decide +kernel
theorem r_reference63_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed 0)=true := by decide +kernel
theorem a_reference63_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed 1)=true := by decide +kernel
theorem rank_r_link63_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0007.r63.bounds ReferenceRankData.CoarseLowerShape.Batch0007.r63 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link63_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0007.a63.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a63 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints63 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell true ReferenceProfileData.CoarseLowerShape.Batch0007.r63.bounds ReferenceRankData.CoarseLowerShape.Batch0007.r63 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile63_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0007.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0007.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link63_checked
    geometry63_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell false ReferenceProfileData.CoarseLowerShape.Batch0007.a63.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a63 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile63_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0007.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0007.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link63_checked
    geometry63_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks63_linked.1,←ranks63_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0007.r63.bounds ReferenceRankData.CoarseLowerShape.Batch0007.a63.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0007.ordered63_checked hr ha ho
theorem frozen_frame63 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63 ReferenceProfileData.CoarseLowerShape.Batch0007.r63.bounds ReferenceProfileData.CoarseLowerShape.Batch0007.a63.bounds
  · rw [←r_profile63_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile63_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry63_linked.2.2.2.2.1
  · exact geometry63_linked.2.2.2.2.2
  · exact r_reference63_checked
  · exact a_reference63_checked
  · exact r_fixed63_linked
  · exact a_fixed63_linked
  · exact time63_checked
  · exact ht
  · exact hw
theorem child_geometry63_checked : ReferenceWeightData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights63 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0015.cert126∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch15_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0015.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0015.cert127∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch15_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0015.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry63_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights126_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry63_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry63_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights127_linked j (List.mem_finRange j))
theorem actual_frozen_frame63 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame63 (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.flow.timeParameter_mem child_geometry63_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights63 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell56),(ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell57),(ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell58),(ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell59),(ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell60),(ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell61),(ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell62),(ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0007.cell63)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0007.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0007.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame56 hz
  · exact fun z hz=>actual_frozen_frame57 hz
  · exact fun z hz=>actual_frozen_frame58 hz
  · exact fun z hz=>actual_frozen_frame59 hz
  · exact fun z hz=>actual_frozen_frame60 hz
  · exact fun z hz=>actual_frozen_frame61 hz
  · exact fun z hz=>actual_frozen_frame62 hz
  · exact fun z hz=>actual_frozen_frame63 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints56 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints57 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints58 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints59 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints60 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints61 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints62 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints63 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry56_linked.1,geometry56_linked.2.1,geometry56_linked.2.2.1,geometry56_linked.2.2.2.1⟩
  · exact ⟨geometry57_linked.1,geometry57_linked.2.1,geometry57_linked.2.2.1,geometry57_linked.2.2.2.1⟩
  · exact ⟨geometry58_linked.1,geometry58_linked.2.1,geometry58_linked.2.2.1,geometry58_linked.2.2.2.1⟩
  · exact ⟨geometry59_linked.1,geometry59_linked.2.1,geometry59_linked.2.2.1,geometry59_linked.2.2.2.1⟩
  · exact ⟨geometry60_linked.1,geometry60_linked.2.1,geometry60_linked.2.2.1,geometry60_linked.2.2.2.1⟩
  · exact ⟨geometry61_linked.1,geometry61_linked.2.1,geometry61_linked.2.2.1,geometry61_linked.2.2.2.1⟩
  · exact ⟨geometry62_linked.1,geometry62_linked.2.1,geometry62_linked.2.2.1,geometry62_linked.2.2.2.1⟩
  · exact ⟨geometry63_linked.1,geometry63_linked.2.1,geometry63_linked.2.2.1,geometry63_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0007.a56.bounds,?_,geometry56_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0007.a56.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile56_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0007.r56.bounds,?_,geometry56_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert56.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0007.r56.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile56_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0007.a57.bounds,?_,geometry57_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0007.a57.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile57_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0007.r57.bounds,?_,geometry57_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert57.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0007.r57.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile57_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0007.a58.bounds,?_,geometry58_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0007.a58.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile58_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0007.r58.bounds,?_,geometry58_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert58.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0007.r58.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile58_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0007.a59.bounds,?_,geometry59_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0007.a59.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile59_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0007.r59.bounds,?_,geometry59_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert59.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0007.r59.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile59_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0007.a60.bounds,?_,geometry60_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0007.a60.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile60_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0007.r60.bounds,?_,geometry60_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert60.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0007.r60.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile60_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0007.a61.bounds,?_,geometry61_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0007.a61.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile61_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0007.r61.bounds,?_,geometry61_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert61.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0007.r61.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile61_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0007.a62.bounds,?_,geometry62_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0007.a62.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile62_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0007.r62.bounds,?_,geometry62_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert62.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0007.r62.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile62_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0007.a63.bounds,?_,geometry63_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0007.a63.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile63_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0007.r63.bounds,?_,geometry63_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0007.cert63.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0007.r63.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile63_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0007.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0007.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0007
