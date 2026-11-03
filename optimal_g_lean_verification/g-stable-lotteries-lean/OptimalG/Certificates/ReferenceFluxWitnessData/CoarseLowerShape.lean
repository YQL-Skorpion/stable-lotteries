import OptimalG.Certificates.ReferenceFluxPointwise
import OptimalG.Certificates.ReferenceOverlayData.CoarseLowerShape.Assembly
namespace OptimalG.Certificates.ReferenceFluxWitnessData.CoarseLowerShape
open Set MeasureTheory Transport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem time_order : (ReferenceActualData.CoarseLowerShape.start:ℝ)≤ReferenceActualData.CoarseLowerShape.finish := by norm_num [ReferenceActualData.CoarseLowerShape.start,ReferenceActualData.CoarseLowerShape.finish]
theorem Z_continuous : ContinuousOn ReferenceAdjointData.CoarseLowerShape.Z (Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish) := by
  simpa only [uIcc_of_le time_order] using ReferenceAdjointData.CoarseLowerShape.Z_spec.2.1.continuousOn
theorem E_continuous : ContinuousOn ReferencePositionData.CoarseLowerShape.exponential (Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish) := by
  have h := intervalIntegral.continuousOn_primitive_interval_left ((intervalIntegrable_iff').mp ReferenceActualData.CoarseLowerShape.alpha_intervalIntegrable)
  change ContinuousOn (Real.exp ∘ fun z : ℝ => ∫ x in z..(ReferenceActualData.CoarseLowerShape.finish:ℝ), ReferenceActualData.CoarseLowerShape.alpha x) _
  simpa only [uIcc_of_le time_order] using Real.continuous_exp.comp_continuousOn h
theorem segment_geometry {seg : ReferenceSegment} (hs : seg∈ReferenceOverlayGeometryData.CoarseLowerShape.segments) :
    (ReferenceActualData.CoarseLowerShape.start:ℝ)≤seg.left.z ∧ seg.left.z<seg.right.z ∧ (seg.right.z:ℝ)≤ReferenceActualData.CoarseLowerShape.finish := by
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hs
  have hb := referenceFlowCoverCheck_bounds ReferenceWeightData.CoarseLowerShape.Assembly.cover_checked (List.mem_map.mpr ⟨c,hc,rfl⟩)
  exact ⟨by exact_mod_cast hb.1,hb.2.1,by exact_mod_cast hb.2.2⟩
theorem force_density_measurable (j : Fin 16) (rank : ReferenceNode→ℚ)
    {seg : ReferenceSegment} (hs : seg∈ReferenceOverlayGeometryData.CoarseLowerShape.segments) :
    Measurable (segmentDensity seg rank (ReferencePositionData.CoarseLowerShape.force j)) := by
  have hg := segment_geometry hs
  exact coordinateForce_density_measurable ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cells
    time_order Z_continuous E_continuous (ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish) j rank hg.2.1 hg.1 hg.2.2
theorem weight_formula (i : Fin 4) {z : ℝ} (hz : z∈Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish) :
    ReferenceAdjointData.CoarseLowerShape.weight i z=(ReferencePositionData.CoarseLowerShape.exponential z/ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish)*
      (if i.val<2 then ReferenceAdjointData.CoarseLowerShape.Z z else 1)*ReferenceAdjointData.CoarseLowerShape.coefficient i z := by
  rw [ReferenceAdjointData.CoarseLowerShape.weight,ReferenceAdjointData.CoarseLowerShape.rho,Variational.affine_solution_adjoint_at time_order
    ReferenceActualData.CoarseLowerShape.alpha_intervalIntegrable ReferenceActualData.CoarseLowerShape.beta_intervalIntegrable ReferenceAdjointData.CoarseLowerShape.Z_spec.2.1
    ReferenceAdjointData.CoarseLowerShape.Z_spec.2.2.2.2 ReferenceAdjointData.CoarseLowerShape.Z_spec.2.2.1 hz]
  exact Variational.reference_weight_power (ReferenceAdjointData.CoarseLowerShape.Z_spec.2.2.2.2 z hz) i
theorem weight_density_measurable (i : Fin 4) (rank : ReferenceNode→ℚ)
    {seg : ReferenceSegment} (hs : seg∈ReferenceOverlayGeometryData.CoarseLowerShape.segments) :
    Measurable (segmentDensity seg rank (ReferenceAdjointData.CoarseLowerShape.weight i)) := by
  have hg := segment_geometry hs
  exact adjointWeight_density_measurable time_order Z_continuous E_continuous
    (referenceCoefficient_measurable ReferenceActualData.CoarseLowerShape.cells i) (ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish) i
    (fun z hz=>weight_formula i hz) rank hg.2.1 hg.1 hg.2.2
theorem force_measurable : Measurable ReferenceOverlayData.CoarseLowerShape.force := by
  unfold ReferenceOverlayData.CoarseLowerShape.force Transport.f
  exact (pushforwardDensity_measurable _ _ (fun seg hs=>force_density_measurable 1 _ hs)).add
    (pushforwardDensity_measurable _ _ (fun seg hs=>force_density_measurable 2 _ hs))
theorem weight_measurable : Measurable ReferenceOverlayData.CoarseLowerShape.weight := by
  unfold ReferenceOverlayData.CoarseLowerShape.weight Transport.W
  apply Measurable.add
  · apply pushforwardDensity_measurable
    intro seg hs
    rw [segmentDensity_add]
    exact (weight_density_measurable 0 _ hs).add (weight_density_measurable 2 _ hs)
  · apply pushforwardDensity_measurable
    intro seg hs
    rw [segmentDensity_add]
    exact (weight_density_measurable 1 _ hs).add (weight_density_measurable 3 _ hs)
noncomputable def potential (r : ℝ) : ℝ := ∫ x in r..(ReferenceCumulativeData.CoarseLowerShapeRank.finish:ℝ),ReferenceOverlayData.CoarseLowerShape.force x
noncomputable def absorptionError (r : ℝ) : ℝ :=
  (potential r-ReferenceOverlayData.CoarseLowerShape.weight r-ReferenceFluxData.CoarseLowerShape.flux)^2/(potential r-ReferenceFluxData.CoarseLowerShape.flux-3)
theorem actual_flux_budget :
    IntervalIntegrable ReferenceOverlayData.CoarseLowerShape.force volume (ReferenceCumulativeData.CoarseLowerShapeRank.start:ℝ) ReferenceCumulativeData.CoarseLowerShapeRank.finish ∧
    (∀ᵐ r ∂volume.restrict (Icc (ReferenceCumulativeData.CoarseLowerShapeRank.start:ℝ) ReferenceCumulativeData.CoarseLowerShapeRank.finish),
      3≤ReferenceOverlayData.CoarseLowerShape.weight r ∧ 0<potential r-ReferenceFluxData.CoarseLowerShape.flux-3) ∧
    (∫ r in (ReferenceCumulativeData.CoarseLowerShapeRank.start:ℝ)..ReferenceCumulativeData.CoarseLowerShapeRank.finish,absorptionError r)<(1/10000:ℝ) := by
  unfold absorptionError potential
  have h := ReferenceFluxCell.checked_measurable_flux_budget
    (by norm_num [ReferenceFluxData.CoarseLowerShape.scale]) (by norm_num [ReferenceFluxData.CoarseLowerShape.multiplier])
    ReferenceFluxData.CoarseLowerShape.Assembly.cells ReferenceFluxData.CoarseLowerShape.Assembly.checked ReferenceFluxData.CoarseLowerShape.Assembly.cover_checked
    ReferenceFluxData.CoarseLowerShape.Assembly.flux_linked ReferenceFluxData.CoarseLowerShape.Assembly.actual_error_budget_checked
    force_measurable weight_measurable ReferenceOverlayData.CoarseLowerShape.Assembly.actual_flux_bounds
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
theorem actual_stieltjes_regular :
    (∀ r∈Icc (ReferenceCumulativeData.CoarseLowerShapeRank.start:ℝ) ReferenceCumulativeData.CoarseLowerShapeRank.finish,0<potential r-ReferenceFluxData.CoarseLowerShape.flux-3) ∧
    (∃ B : ℝ,∀ᵐ r ∂volume.restrict (Icc (ReferenceCumulativeData.CoarseLowerShapeRank.start:ℝ) ReferenceCumulativeData.CoarseLowerShapeRank.finish),|ReferenceOverlayData.CoarseLowerShape.weight r|≤B) ∧
    IntegrableOn absorptionError (Icc (ReferenceCumulativeData.CoarseLowerShapeRank.start:ℝ) ReferenceCumulativeData.CoarseLowerShapeRank.finish) := by
  exact ReferenceFluxCell.checked_stieltjes_flux_regular (by norm_num [ReferenceFluxData.CoarseLowerShape.scale])
    ReferenceFluxData.CoarseLowerShape.Assembly.cells (by norm_num [ReferenceCumulativeData.CoarseLowerShapeRank.start,ReferenceCumulativeData.CoarseLowerShapeRank.finish]) ReferenceFluxData.CoarseLowerShape.Assembly.checked ReferenceFluxData.CoarseLowerShape.Assembly.cover_checked
    ReferenceFluxData.CoarseLowerShape.Assembly.flux_linked actual_flux_budget.1 weight_measurable ReferenceOverlayData.CoarseLowerShape.Assembly.actual_flux_bounds
theorem flux_negative : (ReferenceFluxData.CoarseLowerShape.flux:ℝ)≤-16 := by norm_num [ReferenceFluxData.CoarseLowerShape.flux]
end OptimalG.Certificates.ReferenceFluxWitnessData.CoarseLowerShape
