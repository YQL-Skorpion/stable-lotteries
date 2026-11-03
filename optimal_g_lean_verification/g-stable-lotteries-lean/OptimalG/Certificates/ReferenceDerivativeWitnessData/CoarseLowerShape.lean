import OptimalG.Certificates.ReferenceDerivativePushforward
import OptimalG.Certificates.ReferenceCoercivityData.CoarseLowerShape
namespace OptimalG.Certificates.ReferenceDerivativeWitnessData.CoarseLowerShape
open Set MeasureTheory Transport
open scoped BigOperators
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable def derivative (useR : Bool) (G : StieltjesFunction ℝ) : ℝ→ℝ :=
  referenceDerivative ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cells useR G
noncomputable def xi (G : StieltjesFunction ℝ) : ℝ→Fin 4→ℝ :=
  referenceXi ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cells G
noncomputable def allocated (useR : Bool) (z : ℝ) : ℝ :=
  if useR then ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z else ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z
theorem derivative_lower (useR : Bool) (G : StieltjesFunction ℝ)
    (hG : ∀ᵐ r ∂volume.restrict (Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right),(3/5:ℝ)≤deriv G r) :
    ∀ᵐ z ∂volume.restrict (Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish),(3/5:ℝ)≤derivative useR G z := by
  apply referenceDerivative_ae_lower ReferenceSensitivityData.CoarseLowerShape.makeCell (fun _=>rfl) ReferenceActualData.CoarseLowerShape.cover_checked useR G (by norm_num) hG
  · intro c hc
    rw [←ReferenceTimeData.CoarseLowerShape.Assembly.source_cells] at hc
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
    have hh := Bool.and_eq_true_iff.mp (List.all_eq_true.mp ReferenceTimeData.CoarseLowerShape.Assembly.rank_crop_checked p hp)
    have hr := ReferenceFlowCell.rankCropCheck_order (useR:=useR) (c:=p.1.flow) (by cases useR <;> first | exact hh.2 | exact hh.1)
    cases useR <;> simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢ <;> exact_mod_cast hr
  · intro c hc hpiece
    rw [←ReferenceTimeData.CoarseLowerShape.Assembly.source_cells] at hc
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
    have hh := Bool.and_eq_true_iff.mp (List.all_eq_true.mp ReferenceTimeData.CoarseLowerShape.Assembly.rank_crop_checked p hp)
    cases useR
    · exact ReferenceFlowCell.rankCropCheck_central_image hh.2 hpiece
    · exact ReferenceFlowCell.rankCropCheck_central_image hh.1 hpiece
theorem xi_positive (G : StieltjesFunction ℝ)
    (hG : ∀ᵐ r ∂volume.restrict (Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right),(3/5:ℝ)≤deriv G r) :
    ∀ᵐ z ∂volume.restrict (Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish),∀ i,0<xi G z i := by
  exact referenceXi_ae_positive ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cells G
    ((derivative_lower true G hG).mono (fun z hz=>lt_of_lt_of_le (by norm_num : (0:ℝ)<3/5) hz))
    ((derivative_lower false G hG).mono (fun z hz=>lt_of_lt_of_le (by norm_num : (0:ℝ)<3/5) hz))
theorem allocated_bound (useR : Bool) {z : ℝ} (hz : z∈Ioc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish) : |allocated useR z|≤40 := by
  cases useR
  · exact (abs_add_le _ _).trans (by linarith only [ReferenceAdjointData.CoarseLowerShape.weight_abs_bound hz 1,ReferenceAdjointData.CoarseLowerShape.weight_abs_bound hz 3])
  · exact (abs_add_le _ _).trans (by linarith only [ReferenceAdjointData.CoarseLowerShape.weight_abs_bound hz 0,ReferenceAdjointData.CoarseLowerShape.weight_abs_bound hz 2])
theorem weight_measurable_on_cell (i : Fin 4) {c : ReferenceFlowCell} (hc : c∈ReferencePositionalWitnessData.CoarseLowerShape.cells) :
    AEStronglyMeasurable (ReferenceAdjointData.CoarseLowerShape.weight i) (volume.restrict (Ioo (c.segment.left.z:ℝ) c.segment.right.z)) := by
  let Ze : ℝ→ℝ := fun z=>ReferenceAdjointData.CoarseLowerShape.Z (referenceClamp ReferenceActualData.CoarseLowerShape.start ReferenceActualData.CoarseLowerShape.finish z)
  let Ee : ℝ→ℝ := fun z=>ReferencePositionData.CoarseLowerShape.exponential (referenceClamp ReferenceActualData.CoarseLowerShape.start ReferenceActualData.CoarseLowerShape.finish z)
  have hZ : Measurable Ze := (referenceClamp_comp_continuous ReferenceFirstWitnessData.CoarseLowerShape.time_order ReferenceFluxWitnessData.CoarseLowerShape.Z_continuous).measurable
  have hE : Measurable Ee := (referenceClamp_comp_continuous ReferenceFirstWitnessData.CoarseLowerShape.time_order ReferenceFluxWitnessData.CoarseLowerShape.E_continuous).measurable
  have hm : Measurable (fun z=>(Ee z/ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish)*(if i.val<2 then Ze z else 1)*ReferenceAdjointData.CoarseLowerShape.coefficient i z) := by
    apply Measurable.mul
    · apply Measurable.mul (hE.div_const _)
      split_ifs <;> first | exact hZ | exact measurable_const
    · exact referenceCoefficient_measurable ReferenceActualData.CoarseLowerShape.cells i
  apply hm.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  have hb := referenceFlowCoverCheck_bounds ReferencePositionalWitnessData.CoarseLowerShape.cover_checked hc
  have hwhole : z∈Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish :=
    ⟨(show (ReferenceActualData.CoarseLowerShape.start:ℝ)≤c.segment.left.z by exact_mod_cast hb.1).trans hz.1.le,
      hz.2.le.trans (by exact_mod_cast hb.2.2)⟩
  simpa only [Ze,Ee,referenceClamp_eq hwhole] using (ReferenceFluxWitnessData.CoarseLowerShape.weight_formula i hwhole).symm
theorem allocated_measurable_on_cell (useR : Bool) {c : ReferenceFlowCell} (hc : c∈ReferencePositionalWitnessData.CoarseLowerShape.cells) :
    AEStronglyMeasurable (allocated useR) (volume.restrict (Ioo (c.segment.left.z:ℝ) c.segment.right.z)) := by
  cases useR
  · exact (weight_measurable_on_cell 1 hc).add (weight_measurable_on_cell 3 hc)
  · exact (weight_measurable_on_cell 0 hc).add (weight_measurable_on_cell 2 hc)
theorem test_crop (useR : Bool) (G : StieltjesFunction ℝ) (test : ℝ→ℝ) (htest : test 1=0)
    {c : ReferenceFlowCell} (hc : c∈ReferencePositionalWitnessData.CoarseLowerShape.cells) {z : ℝ}
    (hz : z∈Ioo (c.segment.left.z:ℝ) c.segment.right.z) :
    test (derivative useR G z)=(Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right).indicator (fun r=>test (deriv G r))
      (c.segment.rankMap (if useR then (·.r) else (·.a)) z) := by
  obtain ⟨cert,hcert,rfl⟩ := List.mem_map.mp hc
  obtain ⟨parent,hparent,lo,hi,href⟩ := ReferenceWeightData.CoarseLowerShape.Assembly.refined cert hcert
  have hmem : cert.cell.flow∈ReferencePositionalWitnessData.CoarseLowerShape.cells := List.mem_map.mpr ⟨cert,hcert,rfl⟩
  have hregion := ReferenceFlowCell.rankCropCheck_region (ReferencePositionalWitnessData.CoarseLowerShape.rank_check useR hmem)
    (referenceFlowCoverCheck_bounds ReferencePositionalWitnessData.CoarseLowerShape.cover_checked hmem).2.1 hz
  apply referenceDerivative_refined_test ReferenceSensitivityData.CoarseLowerShape.makeCell (fun _=>rfl) ReferenceActualData.CoarseLowerShape.cover_checked hparent href
    useR G test htest ⟨hz.1,hz.2.le⟩
  · intro hp
    have he : (if useR then cert.cell.flow.rPiece.isSome else cert.cell.flow.aPiece.isSome)=true := by cases useR <;> exact hp
    simpa only [he,if_true] using hregion
  · intro hp
    have he : (if useR then cert.cell.flow.rPiece.isSome else cert.cell.flow.aPiece.isSome)=false := by cases useR <;> exact hp
    simpa only [he,Bool.false_eq_true,if_false] using hregion
theorem test_time_integrable (useR : Bool) (G : StieltjesFunction ℝ) (test : ℝ→ℝ) (htest : test 1=0)
    (hi : IntegrableOn (fun r=>test (deriv G r)) (Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right))
    {c : ReferenceFlowCell} (hc : c∈ReferencePositionalWitnessData.CoarseLowerShape.cells) :
    IntervalIntegrable (fun z=>test (derivative useR G z)*allocated useR z) volume
      (c.segment.left.z:ℝ) c.segment.right.z := by
  have hb := referenceFlowCoverCheck_bounds ReferencePositionalWitnessData.CoarseLowerShape.cover_checked hc
  apply reference_cropped_test_mul_weight_integrable c.segment (if useR then (·.r) else (·.a))
    (by exact_mod_cast hb.2.1) (by
      simp only [ite_apply]
      exact_mod_cast ReferenceFlowCell.rankCropCheck_order (ReferencePositionalWitnessData.CoarseLowerShape.rank_check useR hc)) hi
    (fun z hz=>test_crop useR G test htest hc hz) (allocated_measurable_on_cell useR hc) (B:=40)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  exact allocated_bound useR
    ⟨(show (ReferenceActualData.CoarseLowerShape.start:ℝ)≤c.segment.left.z by exact_mod_cast hb.1).trans_lt hz.1,
      hz.2.le.trans (by exact_mod_cast hb.2.2)⟩
theorem test_density_integrable (useR : Bool) (G : StieltjesFunction ℝ) (test : ℝ→ℝ)
    (hi : IntegrableOn (fun r=>test (deriv G r)) (Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right))
    {c : ReferenceFlowCell} (hc : c∈ReferencePositionalWitnessData.CoarseLowerShape.cells) :
    Integrable (fun r=>segmentDensity c.segment (if useR then (·.r) else (·.a)) (allocated useR) r*
      (Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right).indicator (fun r=>test (deriv G r)) r) := by
  let rank : ReferenceNode→ℚ := if useR then (·.r) else (·.a)
  have ht := referenceFlowCoverCheck_bounds ReferencePositionalWitnessData.CoarseLowerShape.cover_checked hc
  have hr : rank c.segment.left<rank c.segment.right := by
    simpa only [rank,ite_apply] using ReferenceFlowCell.rankCropCheck_order (ReferencePositionalWitnessData.CoarseLowerShape.rank_check useR hc)
  have hpos : 0<c.segment.slope rank := div_pos (sub_pos.mpr hr) (sub_pos.mpr ht.2.1)
  have hposR : (0:ℝ)<c.segment.slope rank := by exact_mod_cast hpos
  have hseg : c.segment∈ReferenceOverlayGeometryData.CoarseLowerShape.segments := by
    obtain ⟨cert,hcert,rfl⟩ := List.mem_map.mp hc
    exact List.mem_map.mpr ⟨cert,hcert,rfl⟩
  apply segmentDensity_cropped_test_integrable c.segment rank (allocated useR) _ hi (B:=40/(c.segment.slope rank:ℝ)) (by positivity)
  · cases useR
    · change Measurable (segmentDensity c.segment rank (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z))
      rw [segmentDensity_add]
      exact (ReferenceFluxWitnessData.CoarseLowerShape.weight_density_measurable 1 rank hseg).add (ReferenceFluxWitnessData.CoarseLowerShape.weight_density_measurable 3 rank hseg)
    · change Measurable (segmentDensity c.segment rank (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z))
      rw [segmentDensity_add]
      exact (ReferenceFluxWitnessData.CoarseLowerShape.weight_density_measurable 0 rank hseg).add (ReferenceFluxWitnessData.CoarseLowerShape.weight_density_measurable 2 rank hseg)
  · intro r hrank
    have hz := ReferenceSegment.inverseRankMap_mem ht.2.1 hpos hrank
    have hb := allocated_bound useR
      ⟨(show (ReferenceActualData.CoarseLowerShape.start:ℝ)≤c.segment.left.z by exact_mod_cast ht.1).trans_lt hz.1,
        hz.2.le.trans (by exact_mod_cast ht.2.2)⟩
    simp only [segmentDensity,if_pos hrank,abs_div,abs_of_pos hposR]
    exact div_le_div_of_nonneg_right hb hposR.le
theorem weighted_test_integrable (G : StieltjesFunction ℝ) (test : ℝ→ℝ) (htest : test 1=0)
    (hi : IntegrableOn (fun r=>test (deriv G r)) (Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right)) :
    IntervalIntegrable (fun z=>∑ i,ReferenceAdjointData.CoarseLowerShape.weight i z*test (xi G z i)) volume (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish := by
  have hR := (referenceFlow_partition_integral _ ReferencePositionalWitnessData.CoarseLowerShape.cover_checked
    (fun c hc=>test_time_integrable true G test htest hi hc)).1
  have hA := (referenceFlow_partition_integral _ ReferencePositionalWitnessData.CoarseLowerShape.cover_checked
    (fun c hc=>test_time_integrable false G test htest hi hc)).1
  convert hR.add hA using 1
  funext z
  rw [xi,referenceXi,four_weighted_rank_test]
  simp only [derivative,allocated,Bool.false_eq_true,if_true,if_false]
  ring
theorem weighted_test_integral (G : StieltjesFunction ℝ) (test : ℝ→ℝ) (htest : test 1=0)
    (hi : IntegrableOn (fun r=>test (deriv G r)) (Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right)) :
    (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,∑ i,ReferenceAdjointData.CoarseLowerShape.weight i z*test (xi G z i))=
      ∫ r in Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,ReferenceOverlayData.CoarseLowerShape.weight r*test (deriv G r) := by
  have hh := reference_weighted_test_integral ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cells G test ReferenceAdjointData.CoarseLowerShape.weight
    ReferencePositionalWitnessData.CoarseLowerShape.cover_checked ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right
    (fun c hc=>by exact_mod_cast ReferenceFlowCell.rankCropCheck_order (ReferencePositionalWitnessData.CoarseLowerShape.rank_check true hc))
    (fun c hc=>by exact_mod_cast ReferenceFlowCell.rankCropCheck_order (ReferencePositionalWitnessData.CoarseLowerShape.rank_check false hc))
    (fun c hc z hz=>test_crop true G test htest hc hz) (fun c hc z hz=>test_crop false G test htest hc hz)
    (fun c hc=>test_time_integrable true G test htest hi hc) (fun c hc=>test_time_integrable false G test htest hi hc)
    (fun c hc=>test_density_integrable true G test hi hc) (fun c hc=>test_density_integrable false G test hi hc)
  simpa only [xi,ReferencePositionalWitnessData.CoarseLowerShape.cells,List.map_map,Function.comp_def,ReferenceOverlayData.CoarseLowerShape.weight,ReferenceOverlayGeometryData.CoarseLowerShape.segments] using hh
theorem actual_derivative_source (G : StieltjesFunction ℝ) :
    IntervalIntegrable (Variational.transportDerivativeSource ReferenceAdjointData.CoarseLowerShape.rho (fun z=>Real.log (ReferenceAdjointData.CoarseLowerShape.Z z))
      (fun z i=>ReferenceAdjointData.CoarseLowerShape.coefficient i z) (xi G) Variational.transportDelta) volume (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish ∧
    (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,Variational.transportDerivativeSource ReferenceAdjointData.CoarseLowerShape.rho (fun z=>Real.log (ReferenceAdjointData.CoarseLowerShape.Z z))
      (fun z i=>ReferenceAdjointData.CoarseLowerShape.coefficient i z) (xi G) Variational.transportDelta z)=ReferenceCoercivityData.CoarseLowerShape.derivativeFlux G := by
  have he : Variational.transportDerivativeSource ReferenceAdjointData.CoarseLowerShape.rho (fun z=>Real.log (ReferenceAdjointData.CoarseLowerShape.Z z))
      (fun z i=>ReferenceAdjointData.CoarseLowerShape.coefficient i z) (xi G) Variational.transportDelta=
      fun z=>∑ i,ReferenceAdjointData.CoarseLowerShape.weight i z*(fun x : ℝ=>x-1) (xi G z i) := by
    funext z
    exact genuine_derivative_source_eq ReferenceAdjointData.CoarseLowerShape.rho (fun z=>Real.log (ReferenceAdjointData.CoarseLowerShape.Z z))
      (fun z i=>ReferenceAdjointData.CoarseLowerShape.coefficient i z) ReferenceAdjointData.CoarseLowerShape.weight (xi G) (fun _=>rfl)
  rw [he]
  exact ⟨weighted_test_integrable G (fun x : ℝ=>x-1) (by norm_num) ((Variational.stieltjes_deriv_integrable G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right).sub (integrable_const 1)),
    weighted_test_integral G (fun x : ℝ=>x-1) (by norm_num) ((Variational.stieltjes_deriv_integrable G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right).sub (integrable_const 1))⟩
theorem actual_entropy_source (G : StieltjesFunction ℝ)
    (hG : ∀ᵐ r ∂volume.restrict (Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right),(3/5:ℝ)≤deriv G r) :
    IntervalIntegrable (Variational.transportEntropySource ReferenceAdjointData.CoarseLowerShape.rho (fun z=>Real.log (ReferenceAdjointData.CoarseLowerShape.Z z))
      (fun z i=>ReferenceAdjointData.CoarseLowerShape.coefficient i z) (xi G) Variational.transportDelta) volume (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish ∧
    (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,Variational.transportEntropySource ReferenceAdjointData.CoarseLowerShape.rho (fun z=>Real.log (ReferenceAdjointData.CoarseLowerShape.Z z))
      (fun z i=>ReferenceAdjointData.CoarseLowerShape.coefficient i z) (xi G) Variational.transportDelta z)=ReferenceCoercivityData.CoarseLowerShape.entropyFlux G := by
  have he : Variational.transportEntropySource ReferenceAdjointData.CoarseLowerShape.rho (fun z=>Real.log (ReferenceAdjointData.CoarseLowerShape.Z z))
      (fun z i=>ReferenceAdjointData.CoarseLowerShape.coefficient i z) (xi G) Variational.transportDelta=
      fun z=>∑ i,ReferenceAdjointData.CoarseLowerShape.weight i z*Variational.transportEntropy (xi G z i) := by
    funext z
    exact genuine_entropy_source_eq ReferenceAdjointData.CoarseLowerShape.rho (fun z=>Real.log (ReferenceAdjointData.CoarseLowerShape.Z z))
      (fun z i=>ReferenceAdjointData.CoarseLowerShape.coefficient i z) ReferenceAdjointData.CoarseLowerShape.weight (xi G) (fun _=>rfl)
  rw [he]
  exact ⟨weighted_test_integrable G Variational.transportEntropy (by norm_num [Variational.transportEntropy]) (Variational.transportEntropy_integrable (Variational.stieltjes_deriv_integrable G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right) (by norm_num : (0:ℝ)<3/5) hG),
    weighted_test_integral G Variational.transportEntropy (by norm_num [Variational.transportEntropy]) (Variational.transportEntropy_integrable (Variational.stieltjes_deriv_integrable G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right) (by norm_num : (0:ℝ)<3/5) hG)⟩
end OptimalG.Certificates.ReferenceDerivativeWitnessData.CoarseLowerShape
