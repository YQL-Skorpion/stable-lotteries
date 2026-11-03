import OptimalG.Certificates.ReferenceFlowTolerances
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Assembly
import OptimalG.Certificates.ReferenceCurveData.CoarseLowerShape
namespace OptimalG.Certificates.ReferenceActualData.CoarseLowerShape
open Set MeasureTheory Transport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def start : ℚ := (7835342428237777/10000000000000000)
def finish : ℚ := (8624179577667147/10000000000000000)
def flowRate : ℚ := 1/500000
def certificates := ReferenceSensitivityData.CoarseLowerShape.Assembly.certificates
def cells : List ReferenceFlowCell := certificates.map (fun c => c.cell.flow)
theorem cover_checked : referenceFlowCoverCheck start finish cells=true := by decide +kernel
theorem polynomials_checked : certificates.all (fun c => c.cell.flow.canonicalPieceCheck)=true := by decide +kernel
theorem pieces_checked : ReferenceCurveData.CoarseLowerShape.pieces=certificates.map (fun c => c.cell.flow.canonicalPiece) := by decide +kernel
noncomputable def referenceCubic : ℝ→ℝ := cubicPrimitive ReferenceCurveData.CoarseLowerShape.tailLam ReferenceCurveData.CoarseLowerShape.tailSlack ReferenceCurveData.CoarseLowerShape.pieces
theorem actual_solution : ∃ Z : ℝ→ℝ,
    Z start=referenceCubic start ∧ AbsolutelyContinuousOnInterval Z start finish ∧
    (∀ᵐ z ∂volume.restrict (Icc (start:ℝ) finish),deriv Z z=
      referenceField ReferenceFlowCell.actualAlpha cells z*Z z+
        referenceField ReferenceFlowCell.actualBeta cells z) ∧
    ∀ z∈Icc (start:ℝ) finish,|Z z-referenceCubic z|≤(flowRate:ℝ)*(z-start) := by
  have hc : trajectoryCheck ReferenceCurveData.CoarseLowerShape.tailLam ReferenceCurveData.CoarseLowerShape.tailSlack
      (certificates.map (fun c => c.cell.flow.canonicalPiece))=true := by
    rw [←pieces_checked]; exact ReferenceCurveData.CoarseLowerShape.assembly_checked
  have h := checked_reference_flow_exists_with_tolerances (epsilon:=(1/1000000:ℝ))
    (scale:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) certificates ReferenceSensitivityData.CoarseLowerShape.Assembly.checked cover_checked hc polynomials_checked
    (by norm_num [start,finish]) (by norm_num)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.flowResidual,ReferenceSensitivityData.CoarseLowerShape.scale])
  rw [←pieces_checked] at h
  have hrate : (flowRate:ℝ)=2*(1/1000000:ℝ) := by norm_num [flowRate]
  simpa only [hrate,cells,referenceCubic] using h
noncomputable def alpha : ℝ→ℝ := referenceField ReferenceFlowCell.actualAlpha cells
noncomputable def beta : ℝ→ℝ := referenceField ReferenceFlowCell.actualBeta cells
theorem alpha_measurable : Measurable alpha := referenceField_measurable _ ReferenceFlowCell.actualAlpha_measurable _
theorem beta_measurable : Measurable beta := referenceField_measurable _ ReferenceFlowCell.actualBeta_measurable _
theorem alpha_intervalIntegrable : IntervalIntegrable alpha volume (start:ℝ) finish := by
  apply referenceField_intervalIntegrable (B:=3) ReferenceFlowCell.actualAlpha (by norm_num [start,finish]) cover_checked ReferenceFlowCell.actualAlpha_measurable
  intro c hc t ht
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  exact (d.checked_bounds_with_tolerances (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (List.all_eq_true.mp ReferenceSensitivityData.CoarseLowerShape.Assembly.checked d hd) ht).2.2.1
theorem beta_intervalIntegrable : IntervalIntegrable beta volume (start:ℝ) finish := by
  apply referenceField_intervalIntegrable (B:=1000) ReferenceFlowCell.actualBeta (by norm_num [start,finish]) cover_checked ReferenceFlowCell.actualBeta_measurable
  intro c hc t ht
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  exact (d.checked_bounds_with_tolerances (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (List.all_eq_true.mp ReferenceSensitivityData.CoarseLowerShape.Assembly.checked d hd) ht).2.2.2.1
end OptimalG.Certificates.ReferenceActualData.CoarseLowerShape
