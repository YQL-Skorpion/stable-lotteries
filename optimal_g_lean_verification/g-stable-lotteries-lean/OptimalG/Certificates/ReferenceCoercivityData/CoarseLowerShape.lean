import OptimalG.Certificates.ReferenceRetainedBudget
import OptimalG.Certificates.ReferencePositionalWitnessData.CoarseLowerShape
import OptimalG.Certificates.TransportTerminalData.CoarseLowerShape
import OptimalG.VariationalTransportAssembly
import OptimalG.VariationalStieltjesIntegrability
namespace OptimalG.Certificates.ReferenceCoercivityData.CoarseLowerShape
open Set MeasureTheory Transport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable def ds (S : ℝ) : ℝ := S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ)
noncomputable def flow (S : ℝ) (G : StieltjesFunction ℝ) : ℝ :=
  ∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,ReferenceTaylorData.CoarseLowerShape.source S G z
noncomputable def derivativeFlux (G : StieltjesFunction ℝ) : ℝ :=
  ∫ r in Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,ReferenceOverlayData.CoarseLowerShape.weight r*(deriv G r-1)
noncomputable def entropyFlux (G : StieltjesFunction ℝ) : ℝ :=
  ∫ r in Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,ReferenceOverlayData.CoarseLowerShape.weight r*Variational.transportEntropy (deriv G r)
theorem terminal_taylor {S : ℝ} (hS : Compact.ScalarRange S) :
    -(RatExpr.logPartial 0 ReferenceEndpointData.CoarseLowerShape.parameters.deficitExpr).evalOne ReferenceEndpointData.CoarseLowerShape.parameters.slack*ds S+
      (650:ℝ)/2*(ds S)^2≤Real.log (ReferenceEndpointData.CoarseLowerShape.parameters.terminalDeficit ReferenceEndpointData.CoarseLowerShape.parameters.slack)-
        Real.log (ReferenceEndpointData.CoarseLowerShape.parameters.terminalDeficit S) := by
  have h0 : (⟨TransportTerminalData.CoarseLowerShape.start,TransportTerminalData.CoarseLowerShape.finish⟩:IntegerInterval).Contains TransportTerminalData.CoarseLowerShape.scale (TransportTerminalData.CoarseLowerShape.params.slack:ℝ) := by
    exact ReferenceHessianWitnessData.CoarseLowerShape.reference_scalar_contains
  have h1 : (⟨TransportTerminalData.CoarseLowerShape.start,TransportTerminalData.CoarseLowerShape.finish⟩:IntegerInterval).Contains TransportTerminalData.CoarseLowerShape.scale S :=
    ReferenceHessianWitnessData.CoarseLowerShape.compact_scalar_contains hS
  have hh := TransportTerminalData.CoarseLowerShape.params.checked_terminal_taylor (by norm_num [TransportTerminalData.CoarseLowerShape.scale]) 650
    (by norm_num [TransportTerminalData.CoarseLowerShape.start,TransportTerminalData.CoarseLowerShape.finish]) TransportTerminalData.CoarseLowerShape.cover_checked TransportTerminalData.CoarseLowerShape.all_checked (ds S) (by
      intro t ht
      apply IntegerInterval.contains_add_segment h0 _ ht
      simpa only [ds,show (TransportTerminalData.CoarseLowerShape.params.slack:ℝ)=(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ) from rfl,
        add_sub_cancel] using h1)
  change -Real.log (ReferenceEndpointData.CoarseLowerShape.parameters.terminalDeficit ReferenceEndpointData.CoarseLowerShape.parameters.slack)-
    (RatExpr.logPartial 0 ReferenceEndpointData.CoarseLowerShape.parameters.deficitExpr).evalOne ReferenceEndpointData.CoarseLowerShape.parameters.slack*ds S+
    (650:ℝ)*(ds S)^2/2≤-Real.log (ReferenceEndpointData.CoarseLowerShape.parameters.terminalDeficit ((ReferenceEndpointData.CoarseLowerShape.parameters.slack:ℝ)+ds S)) at hh
  have he : (ReferenceEndpointData.CoarseLowerShape.parameters.slack:ℝ)+ds S=S := by change (TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ)+(S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))=S; ring
  rw [he] at hh
  nlinarith only [hh]
theorem coefficient_taylor {S : ℝ} (hS : Compact.ScalarRange S)
    (G : StieltjesFunction ℝ) {Jlow : ℝ→ℝ}
    (hobstacle : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,quadratic TransportReferenceData.CoarseLowerShape.data.lam r-S≤Jlow r ∧ Jlow r≤cap TransportReferenceData.CoarseLowerShape.data.lam S r)
    (hmatch : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right ∧ Jlow (G r)=TransportReferenceData.CoarseLowerShape.data.transportPrimitive S r)
    (hsq : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,(G r-r)^2≤2*(ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)*Variational.matchingVariation G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right) :
    (ReferenceBudgetData.CoarseLowerShape.V ReferenceActualData.CoarseLowerShape.finish/ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish)*ds S+
      (∫ r in Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,ReferenceOverlayData.CoarseLowerShape.force r*(G r-r))+
      ((TransportHessianData.CoarseLowerShapeFlow.scalarMass:ℝ)/2)*(ds S)^2-
      (2*(ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)*(TransportHessianData.CoarseLowerShapeFlow.rankMass:ℝ))*Variational.matchingVariation G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right≤flow S G := by
  have hh := ReferenceTaylorData.CoarseLowerShape.integrated_taylor hS G hobstacle hmatch hsq
  have hp := ReferencePositionalWitnessData.CoarseLowerShape.actual_positional_integral G (fun r hr=>(hmatch r hr).1) hsq
  dsimp only [flow,ds]
  nlinarith only [hh,hp]
theorem retained_coercivity {S initial w : ℝ} (hS : Compact.ScalarRange S)
    (G : StieltjesFunction ℝ) {Jlow : ℝ→ℝ}
    (hleft : Function.leftLim G ReferenceDisplacementData.CoarseLowerShape.left=ReferenceDisplacementData.CoarseLowerShape.left)
    (hobstacle : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,quadratic TransportReferenceData.CoarseLowerShape.data.lam r-S≤Jlow r ∧ Jlow r≤cap TransportReferenceData.CoarseLowerShape.data.lam S r)
    (hmatch : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right ∧ Jlow (G r)=TransportReferenceData.CoarseLowerShape.data.transportPrimitive S r)
    (hsq : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,(G r-r)^2≤2*(ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)*Variational.matchingVariation G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right)
    (hderiv : ∀ᵐ r ∂volume.restrict (Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right),(3/5:ℝ)≤deriv G r)
    (hflow : initial+flow S G-derivativeFlux G+entropyFlux G≤w-Real.log (ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish))
    (hfeasible : w≤Real.log (ReferenceEndpointData.CoarseLowerShape.parameters.terminalDeficit S)) :
    ReferenceBudgetData.CoarseLowerShape.violation+initial-(1/10000:ℝ)+ReferenceBudgetData.CoarseLowerShape.firstVariation*ds S+
      (((TransportHessianData.CoarseLowerShapeFlow.scalarMass:ℝ)+650)/2)*(ds S)^2+(ReferenceFluxData.CoarseLowerShape.flux:ℝ)*(G ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.right)+
      (8/3-2*(ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)*(TransportHessianData.CoarseLowerShapeFlow.rankMass:ℝ))*Variational.matchingVariation G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right≤0 := by
  have hf : IntegrableOn ReferenceOverlayData.CoarseLowerShape.force (Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ReferenceDisplacementData.CoarseLowerShape.rank_order).mp ReferenceFluxWitnessData.CoarseLowerShape.actual_flux_budget.1
  obtain ⟨Bweight,hBweight⟩ := ReferenceFluxWitnessData.CoarseLowerShape.actual_stieltjes_regular.2.1
  have hi := Variational.stieltjes_weighted_integrability G ReferenceFluxWitnessData.CoarseLowerShape.weight_measurable.aestronglyMeasurable
    hBweight (by norm_num : (0:ℝ)<3/5) hderiv
  have heps : (∫ r in Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,
      ((∫ t in r..ReferenceDisplacementData.CoarseLowerShape.right,ReferenceOverlayData.CoarseLowerShape.force t)-ReferenceOverlayData.CoarseLowerShape.weight r-ReferenceFluxData.CoarseLowerShape.flux)^2/
        ((∫ t in r..ReferenceDisplacementData.CoarseLowerShape.right,ReferenceOverlayData.CoarseLowerShape.force t)-ReferenceFluxData.CoarseLowerShape.flux-3))≤(1/10000:ℝ) := by
    have hh : (∫ r in ReferenceDisplacementData.CoarseLowerShape.left..ReferenceDisplacementData.CoarseLowerShape.right,ReferenceFluxWitnessData.CoarseLowerShape.absorptionError r)≤(1/10000:ℝ) :=
      ReferenceFluxWitnessData.CoarseLowerShape.actual_flux_budget.2.2.le
    rw [intervalIntegral.integral_of_le ReferenceDisplacementData.CoarseLowerShape.rank_order,
      Measure.restrict_congr_set Ioc_ae_eq_Icc] at hh
    exact hh
  have hh := Variational.stieltjes_coercivity_from_log_flow G ReferenceDisplacementData.CoarseLowerShape.rank_order hleft
    (hmatch ReferenceDisplacementData.CoarseLowerShape.right ⟨ReferenceDisplacementData.CoarseLowerShape.rank_order,le_rfl⟩).1.2 hf hi.1
    (by norm_num : (0:ℝ)≤3) (le_trans ReferenceFluxWitnessData.CoarseLowerShape.flux_negative (by norm_num))
    (ReferenceFluxWitnessData.CoarseLowerShape.actual_flux_budget.2.1.mono (fun r hr=>hr.1)) ReferenceFluxWitnessData.CoarseLowerShape.actual_stieltjes_regular.1
    (hderiv.mono (fun r hr=>lt_of_lt_of_le (by norm_num : (0:ℝ)<3/5) hr))
    ReferenceFluxWitnessData.CoarseLowerShape.actual_stieltjes_regular.2.2 hi.2 heps hflow
    (coefficient_taylor hS G hobstacle hmatch hsq) (terminal_taylor hS) hfeasible
  have hfirst : ReferenceBudgetData.CoarseLowerShape.V ReferenceActualData.CoarseLowerShape.finish/ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish-
      (RatExpr.logPartial 0 ReferenceEndpointData.CoarseLowerShape.parameters.deficitExpr).evalOne ReferenceEndpointData.CoarseLowerShape.parameters.slack=ReferenceBudgetData.CoarseLowerShape.firstVariation := by
    rw [ReferenceBudgetData.CoarseLowerShape.firstVariation,ReferenceBudgetData.CoarseLowerShape.scalar_integral_identity]
  change ReferenceBudgetData.CoarseLowerShape.violation+initial-(1/10000:ℝ)+
    (ReferenceBudgetData.CoarseLowerShape.V ReferenceActualData.CoarseLowerShape.finish/ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish+ -(RatExpr.logPartial 0 ReferenceEndpointData.CoarseLowerShape.parameters.deficitExpr).evalOne ReferenceEndpointData.CoarseLowerShape.parameters.slack)*ds S+
    ((TransportHessianData.CoarseLowerShapeFlow.scalarMass:ℝ)/2+650/2)*(ds S)^2+(ReferenceFluxData.CoarseLowerShape.flux:ℝ)*(G ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.right)+
    (8/9*3-2*(ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)*(TransportHessianData.CoarseLowerShapeFlow.rankMass:ℝ))*Variational.matchingVariation G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right≤0 at hh
  rw [←sub_eq_add_neg,hfirst] at hh
  convert hh using 1 <;> ring
theorem lower_reference_excludes {S initial : ℝ} (G : StieltjesFunction ℝ)
    (hinitial : 0 ≤ initial) (hend : G ReferenceDisplacementData.CoarseLowerShape.right≤ReferenceDisplacementData.CoarseLowerShape.right)
    (hc : ReferenceBudgetData.CoarseLowerShape.violation+initial-(1/10000:ℝ)+ReferenceBudgetData.CoarseLowerShape.firstVariation*ds S+
      (((TransportHessianData.CoarseLowerShapeFlow.scalarMass:ℝ)+650)/2)*(ds S)^2+(ReferenceFluxData.CoarseLowerShape.flux:ℝ)*(G ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.right)+
      (8/3-2*(ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)*(TransportHessianData.CoarseLowerShapeFlow.rankMass:ℝ))*Variational.matchingVariation G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right≤0) : False := by
  have hk : (30:ℝ)≤((TransportHessianData.CoarseLowerShapeFlow.scalarMass:ℝ)+650)/2 := by exact_mod_cast (by linarith [TransportHessianData.CoarseLowerShapeFlow.scalar_margin_checked] : (30:ℚ)≤(TransportHessianData.CoarseLowerShapeFlow.scalarMass+650)/2)
  have hr : (3/10:ℝ)≤8/3-2*(ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)*(TransportHessianData.CoarseLowerShapeFlow.rankMass:ℝ) := by
    have hw : (TransportHessianData.CoarseLowerShapeFlow.rankWidth:ℝ)=ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left := by norm_num [TransportHessianData.CoarseLowerShapeFlow.rankWidth,ReferenceDisplacementData.CoarseLowerShape.left,ReferenceDisplacementData.CoarseLowerShape.right,TransportReferenceData.CoarseLowerShape.data,TransportReferenceData.CoarseLowerShape.leftContact,TransportReferenceData.CoarseLowerShape.rightContact]
    rw [←hw]
    have h := (Rat.cast_le (K := ℝ)).mpr TransportHessianData.CoarseLowerShapeFlow.rank_margin_checked
    simpa only [Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat] using h
  have hs := mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg (ds S))
  have hv := mul_nonneg (le_trans (by norm_num : (0:ℝ)≤3/10) hr) (Variational.matchingVariation_nonneg G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right)
  have he := mul_nonneg_of_nonpos_of_nonpos (le_trans ReferenceFluxWitnessData.CoarseLowerShape.flux_negative (by norm_num)) (sub_nonpos.mpr hend)
  have hb := ReferenceBudgetData.CoarseLowerShape.endpoint_budget
  exact retained_coarse_lower_reference_excludes hb.1 hb.2 hk le_rfl hinitial
    (le_trans ReferenceFluxWitnessData.CoarseLowerShape.flux_negative (by norm_num)) (sub_nonpos.mpr hend)
    (le_trans (by norm_num : (0:ℝ)≤3/10) hr)
    (Variational.matchingVariation_nonneg G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right) hc

end OptimalG.Certificates.ReferenceCoercivityData.CoarseLowerShape
