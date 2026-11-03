import OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
import OptimalG.Certificates.ReferenceAuxiliaryData.CoarseLowerShape
import OptimalG.Certificates.ReferenceEndpointTightData.CoarseLowerShape
namespace OptimalG.Certificates.ReferenceBudgetData.CoarseLowerShape
open Set MeasureTheory Transport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable def alphaS : ℝ→ℝ := referenceField (fun f=>(ReferenceSensitivityData.CoarseLowerShape.makeCell f).actualAlphaS) ReferenceActualData.CoarseLowerShape.cells
noncomputable def betaS : ℝ→ℝ := referenceField (fun f=>(ReferenceSensitivityData.CoarseLowerShape.makeCell f).actualBetaS) ReferenceActualData.CoarseLowerShape.cells
theorem alphaS_intervalIntegrable : IntervalIntegrable alphaS volume (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish := by
  apply referenceField_intervalIntegrable (B:=1000) (fun f=>(ReferenceSensitivityData.CoarseLowerShape.makeCell f).actualAlphaS)
    (by norm_num [ReferenceActualData.CoarseLowerShape.start,ReferenceActualData.CoarseLowerShape.finish]) ReferenceActualData.CoarseLowerShape.cover_checked
    (fun c=>(ReferenceSensitivityData.CoarseLowerShape.makeCell c).actualAlphaS_measurable)
  intro c hc t ht
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  have he : ReferenceSensitivityData.CoarseLowerShape.makeCell d.cell.flow=d.cell := of_decide_eq_true (List.all_eq_true.mp ReferenceAuxiliaryData.CoarseLowerShape.scalar_checked d hd)
  rw [he]
  exact (d.checked_bounds_with_tolerances (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (List.all_eq_true.mp ReferenceSensitivityData.CoarseLowerShape.Assembly.checked d hd) ht).2.2.2.2.1
theorem betaS_intervalIntegrable : IntervalIntegrable betaS volume (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish := by
  apply referenceField_intervalIntegrable (B:=100000) (fun f=>(ReferenceSensitivityData.CoarseLowerShape.makeCell f).actualBetaS)
    (by norm_num [ReferenceActualData.CoarseLowerShape.start,ReferenceActualData.CoarseLowerShape.finish]) ReferenceActualData.CoarseLowerShape.cover_checked
    (fun c=>(ReferenceSensitivityData.CoarseLowerShape.makeCell c).actualBetaS_measurable)
  intro c hc t ht
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  have he : ReferenceSensitivityData.CoarseLowerShape.makeCell d.cell.flow=d.cell := of_decide_eq_true (List.all_eq_true.mp ReferenceAuxiliaryData.CoarseLowerShape.scalar_checked d hd)
  rw [he]
  exact (d.checked_bounds_with_tolerances (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (List.all_eq_true.mp ReferenceSensitivityData.CoarseLowerShape.Assembly.checked d hd) ht).2.2.2.2.2
noncomputable def V : ℝ→ℝ := Classical.choose (ReferenceAuxiliaryData.CoarseLowerShape.actual_auxiliary ReferenceAdjointData.CoarseLowerShape.Z ReferenceAdjointData.CoarseLowerShape.Z_spec.2.1 ReferenceAdjointData.CoarseLowerShape.Z_spec.2.2.2.1)
theorem V_spec :
    V ReferenceActualData.CoarseLowerShape.start=0 ∧ AbsolutelyContinuousOnInterval V ReferenceActualData.CoarseLowerShape.start ReferenceActualData.CoarseLowerShape.finish ∧
    (∀ᵐ z ∂volume.restrict (Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish),
      deriv V z=ReferenceActualData.CoarseLowerShape.alpha z*V z+(alphaS z*ReferenceAdjointData.CoarseLowerShape.Z z+betaS z)) ∧
    (∀ z∈Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish,|V z-ReferenceAuxiliaryData.CoarseLowerShape.variationCubic z|≤(ReferenceAuxiliaryData.CoarseLowerShape.auxiliaryRate:ℝ)*(z-ReferenceActualData.CoarseLowerShape.start)) :=
  Classical.choose_spec (ReferenceAuxiliaryData.CoarseLowerShape.actual_auxiliary ReferenceAdjointData.CoarseLowerShape.Z ReferenceAdjointData.CoarseLowerShape.Z_spec.2.1 ReferenceAdjointData.CoarseLowerShape.Z_spec.2.2.2.1)
theorem scalar_integral_identity :
    (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,ReferenceAdjointData.CoarseLowerShape.rho z*(alphaS z+betaS z/ReferenceAdjointData.CoarseLowerShape.Z z))=
      V ReferenceActualData.CoarseLowerShape.finish/ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish := by
  exact Variational.reference_weighted_scalar_variation
    (by norm_num [ReferenceActualData.CoarseLowerShape.start,ReferenceActualData.CoarseLowerShape.finish]) ReferenceActualData.CoarseLowerShape.alpha_intervalIntegrable ReferenceActualData.CoarseLowerShape.beta_intervalIntegrable
    alphaS_intervalIntegrable betaS_intervalIntegrable ReferenceAdjointData.CoarseLowerShape.Z_spec.2.1 ReferenceAdjointData.CoarseLowerShape.Z_spec.2.2.2.2 ReferenceAdjointData.CoarseLowerShape.Z_spec.2.2.1
    V_spec.2.1 V_spec.1 V_spec.2.2.1
theorem Z_endpoint_contains : ReferenceEndpointData.CoarseLowerShape.certificate.flowDeficit.Contains ReferenceEndpointData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish) := by
  have hg := ReferenceEndpointLinkData.CoarseLowerShape.X_last_geometry
  have hfinish : ReferenceCurveData.CoarseLowerShape.piece347.hi=ReferenceActualData.CoarseLowerShape.finish := hg.2
  apply checked_trajectory_endpoint ReferenceCurveData.CoarseLowerShape.assembly_checked ReferenceEndpointLinkData.CoarseLowerShape.X_last_member hg.1 ReferenceEndpointLinkData.CoarseLowerShape.X_endpoint_checked
  rw [hfinish]
  convert ReferenceAdjointData.CoarseLowerShape.Z_spec.2.2.2.1 ReferenceActualData.CoarseLowerShape.finish ⟨by norm_num [ReferenceActualData.CoarseLowerShape.start,ReferenceActualData.CoarseLowerShape.finish],le_rfl⟩ using 1 <;> norm_num [ReferenceActualData.CoarseLowerShape.flowRate,ReferenceActualData.CoarseLowerShape.start,ReferenceActualData.CoarseLowerShape.finish,ReferenceAuxiliaryData.CoarseLowerShape.auxiliaryRate,ReferenceAuxiliaryData.CoarseLowerShape.auxiliaryTolerance]
  all_goals rfl
theorem V_endpoint_contains : ReferenceEndpointData.CoarseLowerShape.certificate.flowVariation.Contains ReferenceEndpointData.CoarseLowerShape.scale (V ReferenceActualData.CoarseLowerShape.finish) := by
  have hg := ReferenceEndpointLinkData.CoarseLowerShape.V_last_geometry
  have hfinish : ReferenceSensitivityCurveData.CoarseLowerShape.piece347.hi=ReferenceActualData.CoarseLowerShape.finish := hg.2
  apply checked_trajectory_endpoint ReferenceSensitivityCurveData.CoarseLowerShape.assembly_checked ReferenceEndpointLinkData.CoarseLowerShape.V_last_member hg.1 ReferenceEndpointLinkData.CoarseLowerShape.V_endpoint_checked
  rw [hfinish]
  convert V_spec.2.2.2 ReferenceActualData.CoarseLowerShape.finish ⟨by norm_num [ReferenceActualData.CoarseLowerShape.start,ReferenceActualData.CoarseLowerShape.finish],le_rfl⟩ using 1 <;> norm_num [ReferenceActualData.CoarseLowerShape.flowRate,ReferenceActualData.CoarseLowerShape.start,ReferenceActualData.CoarseLowerShape.finish,ReferenceAuxiliaryData.CoarseLowerShape.auxiliaryRate,ReferenceAuxiliaryData.CoarseLowerShape.auxiliaryTolerance]
  all_goals rfl
noncomputable def violation : ℝ := Real.log (ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish)-
  Real.log (ReferenceEndpointData.CoarseLowerShape.parameters.terminalDeficit ReferenceEndpointData.CoarseLowerShape.parameters.slack)
noncomputable def firstVariation : ℝ :=
  (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,ReferenceAdjointData.CoarseLowerShape.rho z*(alphaS z+betaS z/ReferenceAdjointData.CoarseLowerShape.Z z))-
    (RatExpr.logPartial 0 ReferenceEndpointData.CoarseLowerShape.parameters.deficitExpr).evalOne ReferenceEndpointData.CoarseLowerShape.parameters.slack
theorem endpoint_budget : (1/2500)≤violation ∧ |firstVariation|≤(1/20) := by
  have hh := ReferenceEndpointTightData.CoarseLowerShape.certificate.checked_endpoints (by norm_num [ReferenceEndpointData.CoarseLowerShape.scale]) (by norm_num)
    ReferenceEndpointTightData.CoarseLowerShape.checked Z_endpoint_contains V_endpoint_contains
  have hV : ReferenceEndpointTightData.CoarseLowerShape.certificate.firstVariation.Contains ReferenceEndpointData.CoarseLowerShape.scale firstVariation := by
    rw [firstVariation,scalar_integral_identity]
    exact hh.2.2.2
  have hA := IntegerInterval.abs_bound (s:=ReferenceEndpointData.CoarseLowerShape.scale) (by norm_num [ReferenceEndpointData.CoarseLowerShape.scale]) hV
  constructor
  · exact ReferenceEndpointTightData.CoarseLowerShape.violation_lower.trans hh.2.2.1
  · exact hA.trans ReferenceEndpointTightData.CoarseLowerShape.firstVariation_abs
end OptimalG.Certificates.ReferenceBudgetData.CoarseLowerShape
