import OptimalG.Certificates.ReferenceDisplacementCrop
import OptimalG.Certificates.ReferenceRankCropCheck
import OptimalG.Certificates.ReferenceTaylorData.CoarseLowerShape
import OptimalG.Certificates.ReferenceFluxWitnessData.CoarseLowerShape
namespace OptimalG.Certificates.ReferencePositionalWitnessData.CoarseLowerShape
open Set MeasureTheory Transport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cells : List ReferenceFlowCell := ReferenceWeightData.CoarseLowerShape.Assembly.certificates.map (fun c=>c.cell.flow)
theorem cover_checked : referenceFlowCoverCheck ReferenceActualData.CoarseLowerShape.start ReferenceActualData.CoarseLowerShape.finish cells=true := ReferenceWeightData.CoarseLowerShape.Assembly.cover_checked
theorem rank_check (useR : Bool) {c : ReferenceFlowCell} (hc : c∈cells) :
    c.rankCropCheck TransportReferenceData.CoarseLowerShape.data.leftContact TransportReferenceData.CoarseLowerShape.data.rightContact useR=true := by
  obtain ⟨cert,hcert,rfl⟩ := List.mem_map.mp hc
  have hh := Bool.and_eq_true_iff.mp (List.all_eq_true.mp ReferenceWeightData.CoarseLowerShape.Assembly.rank_crop_checked cert hcert)
  cases useR
  · exact hh.2
  · exact hh.1
theorem crop_identity (useR : Bool) (G : StieltjesFunction ℝ)
    {c : ReferenceFlowCell} (hc : c∈cells) {z : ℝ}
    (hz : z∈Ioo (c.segment.left.z:ℝ) c.segment.right.z) :
    ReferenceDisplacementData.CoarseLowerShape.displacement useR G z=(Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right).indicator (fun r=>G r-r)
      (c.segment.rankMap (if useR then (·.r) else (·.a)) z) := by
  obtain ⟨cert,hcert,rfl⟩ := List.mem_map.mp hc
  obtain ⟨parent,hparent,lo,hi,href⟩ := ReferenceWeightData.CoarseLowerShape.Assembly.refined cert hcert
  have hmem : cert.cell.flow∈cells := List.mem_map.mpr ⟨cert,hcert,rfl⟩
  have hregion := ReferenceFlowCell.rankCropCheck_region (rank_check useR hmem)
    (referenceFlowCoverCheck_bounds cover_checked hmem).2.1 hz
  apply referenceDisplacement_refined_crop ReferenceSensitivityData.CoarseLowerShape.makeCell (fun _=>rfl) ReferenceActualData.CoarseLowerShape.cover_checked
    hparent href useR G ⟨hz.1,hz.2.le⟩
  · intro hpiece
    have hp : (if useR then cert.cell.flow.rPiece.isSome else cert.cell.flow.aPiece.isSome)=true := by
      cases useR <;> exact hpiece
    simpa only [hp,if_true] using hregion
  · intro hpiece
    have hp : (if useR then cert.cell.flow.rPiece.isSome else cert.cell.flow.aPiece.isSome)=false := by
      cases useR <;> exact hpiece
    simpa only [hp,Bool.false_eq_true,if_false] using hregion
theorem local_integrable (useR : Bool) (j : Fin 16) (hj : j=1 ∨ j=2)
    (G : StieltjesFunction ℝ) (hG : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right)
    (hsq : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,(G r-r)^2≤2*(ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)*Variational.matchingVariation G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right)
    {c : ReferenceFlowCell} (hc : c∈cells) :
    IntervalIntegrable (fun z=>ReferenceDisplacementData.CoarseLowerShape.displacement useR G z*ReferencePositionData.CoarseLowerShape.force j z) volume
      (c.segment.left.z:ℝ) c.segment.right.z := by
  have hb := referenceFlowCoverCheck_bounds cover_checked hc
  apply (ReferenceDisplacementData.CoarseLowerShape.displacement_force_integrable useR j hj G hG hsq).mono_set
  rw [uIcc_of_le ReferenceFirstWitnessData.CoarseLowerShape.time_order,uIcc_of_le (show (c.segment.left.z:ℝ)≤c.segment.right.z by exact_mod_cast hb.2.1.le)]
  exact Icc_subset_Icc (by exact_mod_cast hb.1) (by exact_mod_cast hb.2.2)
theorem density_integrable (useR : Bool) (j : Fin 16) (hj : j=1 ∨ j=2)
    (G : StieltjesFunction ℝ) (hG : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right)
    {c : ReferenceFlowCell} (hc : c∈cells) :
    Integrable (fun r=>segmentDensity c.segment (if useR then (·.r) else (·.a)) (ReferencePositionData.CoarseLowerShape.force j) r*
      (Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right).indicator (fun r=>G r-r) r) := by
  let rank : ReferenceNode→ℚ := if useR then (·.r) else (·.a)
  have ht := referenceFlowCoverCheck_bounds cover_checked hc
  have hr : rank c.segment.left<rank c.segment.right := by
    simpa only [rank,ite_apply] using ReferenceFlowCell.rankCropCheck_order (rank_check useR hc)
  have hpos : 0<c.segment.slope rank := div_pos (sub_pos.mpr hr) (sub_pos.mpr ht.2.1)
  have hposR : (0:ℝ)<c.segment.slope rank := by exact_mod_cast hpos
  have hseg : c.segment∈ReferenceOverlayGeometryData.CoarseLowerShape.segments := by
    obtain ⟨cert,hcert,rfl⟩ := List.mem_map.mp hc
    exact List.mem_map.mpr ⟨cert,hcert,rfl⟩
  apply segmentDensity_cropped_displacement_integrable c.segment rank (ReferencePositionData.CoarseLowerShape.force j)
    ReferenceDisplacementData.CoarseLowerShape.rank_order G.mono.measurable hG (B:=100/(c.segment.slope rank:ℝ)) (by positivity)
    (ReferenceFluxWitnessData.CoarseLowerShape.force_density_measurable j rank hseg)
  intro r hrank
  have hz := ReferenceSegment.inverseRankMap_mem ht.2.1 hpos hrank
  have hwhole : c.segment.inverseRankMap rank r∈Ioc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish :=
    ⟨(show (ReferenceActualData.CoarseLowerShape.start:ℝ)≤c.segment.left.z by exact_mod_cast ht.1).trans_lt hz.1,
      hz.2.le.trans (by exact_mod_cast ht.2.2)⟩
  have hb : |ReferencePositionData.CoarseLowerShape.force j (c.segment.inverseRankMap rank r)|≤100 := by
    rcases hj with rfl | rfl
    · exact (ReferencePositionData.CoarseLowerShape.Assembly.global_bounds hwhole).1
    · exact (ReferencePositionData.CoarseLowerShape.Assembly.global_bounds hwhole).2
  simp only [segmentDensity,if_pos hrank,abs_div,abs_of_pos hposR]
  exact div_le_div_of_nonneg_right hb hposR.le
theorem actual_positional_integral (G : StieltjesFunction ℝ)
    (hG : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right)
    (hsq : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,(G r-r)^2≤2*(ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)*Variational.matchingVariation G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right) :
    (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,ReferenceDisplacementData.CoarseLowerShape.displacement true G z*ReferencePositionData.CoarseLowerShape.force 1 z)+
      (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,ReferenceDisplacementData.CoarseLowerShape.displacement false G z*ReferencePositionData.CoarseLowerShape.force 2 z)=
      ∫ r in Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,ReferenceOverlayData.CoarseLowerShape.force r*(G r-r) := by
  have h := reference_two_positional_pushforwards cover_checked
    (ReferenceDisplacementData.CoarseLowerShape.displacement true G) (ReferenceDisplacementData.CoarseLowerShape.displacement false G) (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
    (fun r=>G r-r) ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right
    (fun c hc=>by exact_mod_cast ReferenceFlowCell.rankCropCheck_order (rank_check true hc))
    (fun c hc=>by exact_mod_cast ReferenceFlowCell.rankCropCheck_order (rank_check false hc))
    (fun c hc z hz=>crop_identity true G hc hz) (fun c hc z hz=>crop_identity false G hc hz)
    (fun c hc=>local_integrable true 1 (Or.inl rfl) G hG hsq hc)
    (fun c hc=>local_integrable false 2 (Or.inr rfl) G hG hsq hc)
    (fun c hc=>density_integrable true 1 (Or.inl rfl) G hG hc)
    (fun c hc=>density_integrable false 2 (Or.inr rfl) G hG hc)
  rw [intervalIntegral.integral_add
    (ReferenceDisplacementData.CoarseLowerShape.displacement_force_integrable true 1 (Or.inl rfl) G hG hsq)
    (ReferenceDisplacementData.CoarseLowerShape.displacement_force_integrable false 2 (Or.inr rfl) G hG hsq)] at h
  simpa only [cells,List.map_map,Function.comp_def,ReferenceOverlayData.CoarseLowerShape.force,ReferenceOverlayGeometryData.CoarseLowerShape.segments] using h
end OptimalG.Certificates.ReferencePositionalWitnessData.CoarseLowerShape
