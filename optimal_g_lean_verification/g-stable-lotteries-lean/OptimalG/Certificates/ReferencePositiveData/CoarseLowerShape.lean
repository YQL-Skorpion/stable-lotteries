import OptimalG.Certificates.ReferencePositiveTolerance
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Assembly
namespace OptimalG.Certificates.ReferencePositiveData.CoarseLowerShape
open Set MeasureTheory Transport
theorem actual_positive_solution : ∃ Z : ℝ→ℝ,
    Z ReferenceActualData.CoarseLowerShape.start=ReferenceActualData.CoarseLowerShape.referenceCubic ReferenceActualData.CoarseLowerShape.start ∧
    AbsolutelyContinuousOnInterval Z ReferenceActualData.CoarseLowerShape.start ReferenceActualData.CoarseLowerShape.finish ∧
    (∀ᵐ z ∂volume.restrict (Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish),
      deriv Z z=ReferenceActualData.CoarseLowerShape.alpha z*Z z+ReferenceActualData.CoarseLowerShape.beta z) ∧
    (∀ z∈Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish,|Z z-ReferenceActualData.CoarseLowerShape.referenceCubic z|≤(ReferenceActualData.CoarseLowerShape.flowRate:ℝ)*(z-ReferenceActualData.CoarseLowerShape.start)) ∧
    (∀ z∈Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish,0<Z z) := by
  obtain ⟨Z,hinit,hac,hder,herr⟩ := ReferenceActualData.CoarseLowerShape.actual_solution
  refine ⟨Z,hinit,hac,hder,herr,?_⟩
  have hpieces : ReferenceActualData.CoarseLowerShape.cells.map ReferenceFlowCell.canonicalPiece=ReferenceCurveData.CoarseLowerShape.pieces := by
    simpa only [ReferenceActualData.CoarseLowerShape.cells,List.map_map,Function.comp_def] using ReferenceActualData.CoarseLowerShape.pieces_checked.symm
  apply checked_reference_positive_with_error (rate:=(ReferenceActualData.CoarseLowerShape.flowRate:ℝ)) (s:=ReferenceWeightData.CoarseLowerShape.scale) (k:=ReferenceWeightData.CoarseLowerShape.multiplier)
    (L:=ReferenceCurveData.CoarseLowerShape.tailLam) (S:=ReferenceCurveData.CoarseLowerShape.tailSlack)
    (cs:=ReferenceWeightData.CoarseLowerShape.Assembly.certificates)
    (error:=fun c=>(c.cell.flow.segment.right.z-c.start)/500000)
    (by norm_num [ReferenceWeightData.CoarseLowerShape.scale]) (by norm_num [ReferenceWeightData.CoarseLowerShape.multiplier]) ReferenceActualData.CoarseLowerShape.cells
    (by norm_num [ReferenceActualData.CoarseLowerShape.start,ReferenceActualData.CoarseLowerShape.finish]) ReferenceActualData.CoarseLowerShape.cover_checked
  · rw [hpieces]
    exact ReferenceCurveData.CoarseLowerShape.assembly_checked
  · simpa only [ReferenceActualData.CoarseLowerShape.cells,List.all_map,Function.comp_def] using ReferenceActualData.CoarseLowerShape.polynomials_checked
  · exact ReferenceWeightData.CoarseLowerShape.Assembly.checked
  · exact ReferenceWeightData.CoarseLowerShape.Assembly.positivity_checked
  · exact ReferenceWeightData.CoarseLowerShape.Assembly.cover_checked
  · exact ReferenceWeightData.CoarseLowerShape.Assembly.refined
  · norm_num [ReferenceActualData.CoarseLowerShape.flowRate]
  · intro c hc
    have he := of_decide_eq_true (List.all_eq_true.mp ReferenceWeightData.CoarseLowerShape.Assembly.starts_checked c hc)
    rw [he]
    simp only [Rat.cast_div,Rat.cast_sub,Rat.cast_ofNat,ReferenceActualData.CoarseLowerShape.flowRate]
    exact le_of_eq (by ring)
  · simpa only [hpieces,ReferenceActualData.CoarseLowerShape.referenceCubic] using herr
end OptimalG.Certificates.ReferencePositiveData.CoarseLowerShape
