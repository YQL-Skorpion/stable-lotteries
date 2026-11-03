import OptimalG.Certificates.ReferenceAuxiliaryTolerances
import OptimalG.Certificates.ReferenceDataEquality
import OptimalG.Certificates.ReferenceActualData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityCurveData.CoarseLowerShape
namespace OptimalG.Certificates.ReferenceAuxiliaryData.CoarseLowerShape
open Set MeasureTheory Transport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def certificates := ReferenceActualData.CoarseLowerShape.certificates
def auxiliaryTolerance : ℚ := 1/200
def auxiliaryRate : ℚ := 2*(auxiliaryTolerance+1000*(ReferenceActualData.CoarseLowerShape.flowRate*(ReferenceActualData.CoarseLowerShape.finish-ReferenceActualData.CoarseLowerShape.start)))
theorem polynomials_checked : certificates.all (·.canonicalAuxiliaryPieceCheck)=true := by decide +kernel
theorem pieces_checked : ReferenceSensitivityCurveData.CoarseLowerShape.pieces=certificates.map (·.canonicalAuxiliaryPiece) := by decide +kernel
theorem initial_checked : auxiliaryInitialZeroCheck certificates=true := by decide +kernel
theorem scalar_checked : certificates.all (fun c => decide (ReferenceSensitivityData.CoarseLowerShape.makeCell c.cell.flow=c.cell))=true := by decide +kernel
noncomputable def variationCubic : ℝ→ℝ := cubicPrimitive ReferenceSensitivityCurveData.CoarseLowerShape.tailLam ReferenceSensitivityCurveData.CoarseLowerShape.tailSlack ReferenceSensitivityCurveData.CoarseLowerShape.pieces
theorem actual_auxiliary (Z : ℝ→ℝ) (hAC : AbsolutelyContinuousOnInterval Z ReferenceActualData.CoarseLowerShape.start ReferenceActualData.CoarseLowerShape.finish)
    (hZ : ∀z∈Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish,
      |Z z-ReferenceActualData.CoarseLowerShape.referenceCubic z|≤(ReferenceActualData.CoarseLowerShape.flowRate:ℝ)*(z-ReferenceActualData.CoarseLowerShape.start)) :
    ∃ V : ℝ→ℝ,V ReferenceActualData.CoarseLowerShape.start=0 ∧ AbsolutelyContinuousOnInterval V ReferenceActualData.CoarseLowerShape.start ReferenceActualData.CoarseLowerShape.finish ∧
      (∀ᵐ z ∂volume.restrict (Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish),deriv V z=
        referenceField ReferenceFlowCell.actualAlpha ReferenceActualData.CoarseLowerShape.cells z*V z+
          (referenceField (fun f=>(ReferenceSensitivityData.CoarseLowerShape.makeCell f).actualAlphaS) ReferenceActualData.CoarseLowerShape.cells z*Z z+
            referenceField (fun f=>(ReferenceSensitivityData.CoarseLowerShape.makeCell f).actualBetaS) ReferenceActualData.CoarseLowerShape.cells z)) ∧
      ∀z∈Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish,|V z-variationCubic z|≤(auxiliaryRate:ℝ)*(z-ReferenceActualData.CoarseLowerShape.start) := by
  have hX : trajectoryCheck ReferenceCurveData.CoarseLowerShape.tailLam ReferenceCurveData.CoarseLowerShape.tailSlack
      (certificates.map (fun c=>c.cell.flow.canonicalPiece))=true := by
    simpa only [certificates,←ReferenceActualData.CoarseLowerShape.pieces_checked] using
      ReferenceCurveData.CoarseLowerShape.assembly_checked
  have hY : trajectoryCheck ReferenceSensitivityCurveData.CoarseLowerShape.tailLam ReferenceSensitivityCurveData.CoarseLowerShape.tailSlack
      (certificates.map (·.canonicalAuxiliaryPiece))=true := by
    rw [←pieces_checked]; exact ReferenceSensitivityCurveData.CoarseLowerShape.assembly_checked
  have h := checked_reference_auxiliary_flow_exists_with_tolerances (scale:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (rateX:=(ReferenceActualData.CoarseLowerShape.flowRate:ℝ)) (etaAux:=(auxiliaryTolerance:ℝ))
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) certificates ReferenceSensitivityData.CoarseLowerShape.Assembly.checked ReferenceSensitivityData.CoarseLowerShape.makeCell
    (fun c hc => of_decide_eq_true (List.all_eq_true.mp scalar_checked c hc))
    ReferenceActualData.CoarseLowerShape.cover_checked hX hY ReferenceActualData.CoarseLowerShape.polynomials_checked polynomials_checked initial_checked
    (by norm_num [ReferenceActualData.CoarseLowerShape.start,ReferenceActualData.CoarseLowerShape.finish]) (by norm_num [ReferenceActualData.CoarseLowerShape.flowRate])
    (by norm_num [auxiliaryTolerance])
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.auxiliaryResidual,ReferenceSensitivityData.CoarseLowerShape.scale,auxiliaryTolerance]) hAC
    (by simpa only [ReferenceActualData.CoarseLowerShape.referenceCubic,certificates,
      ←ReferenceActualData.CoarseLowerShape.pieces_checked] using hZ)
  rw [←pieces_checked] at h
  simpa only [auxiliaryRate,variationCubic,certificates,ReferenceActualData.CoarseLowerShape.cells,
    Rat.cast_mul,Rat.cast_add,Rat.cast_sub,Rat.cast_ofNat] using h
end OptimalG.Certificates.ReferenceAuxiliaryData.CoarseLowerShape
