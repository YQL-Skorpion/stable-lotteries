import OptimalG.Certificates.ReferenceGlobalTolerance
import OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
namespace OptimalG.Certificates.ReferencePositionData.CoarseLowerShape
open Set MeasureTheory Transport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def scale : ℕ := 1461501637330902918203684832716283019655932542976
def multiplier : ℕ := 1208925819614629174706176
theorem scale_eq : scale=multiplier*ReferenceWeightData.CoarseLowerShape.scale := by decide +kernel
noncomputable def exponential (z : ℝ) : ℝ := Real.exp (∫ x in z..(ReferenceActualData.CoarseLowerShape.finish:ℝ),ReferenceActualData.CoarseLowerShape.alpha x)
noncomputable def force (j : Fin 16) : ℝ→ℝ := referenceCoordinateForce ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cells ReferenceAdjointData.CoarseLowerShape.Z exponential (ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish) j
theorem actual_force {c : ReferencePositionCell} {w : ReferenceWeightCertificate}
    (hw : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates)
    (hc : c.check scale 1=true)
    (hl : c.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale multiplier w ((w.cell.flow.segment.right.z-w.start)/500000)=true)
    (hcell : c.cell=ReferenceSensitivityData.CoarseLowerShape.makeCell w.cell.flow)
    {z : ℝ} (hz : z∈Ioc (w.cell.flow.segment.left.z:ℝ) w.cell.flow.segment.right.z) :
    c.force.Contains scale (force c.coordinate z) := by
  obtain ⟨parent,hp,lo,hi,hr⟩ := ReferenceWeightData.CoarseLowerShape.Assembly.refined w hw
  have hpieces : ReferenceActualData.CoarseLowerShape.cells.map ReferenceFlowCell.canonicalPiece=ReferenceCurveData.CoarseLowerShape.pieces := by
    simpa only [ReferenceActualData.CoarseLowerShape.cells,List.map_map,Function.comp_def] using ReferenceActualData.CoarseLowerShape.pieces_checked.symm
  have hpoly : ReferenceActualData.CoarseLowerShape.cells.all ReferenceFlowCell.canonicalPieceCheck=true := by
    simpa only [ReferenceActualData.CoarseLowerShape.cells,List.all_map,Function.comp_def] using ReferenceActualData.CoarseLowerShape.polynomials_checked
  have hpiece : parent.canonicalPiece∈ReferenceCurveData.CoarseLowerShape.pieces := by
    rw [←hpieces]
    exact List.mem_map.mpr ⟨parent,hp,rfl⟩
  have hstart : w.start=ReferenceActualData.CoarseLowerShape.start := of_decide_eq_true (List.all_eq_true.mp ReferenceWeightData.CoarseLowerShape.Assembly.starts_checked w hw)
  have hterm : w.cell.terminal=ReferenceWeightData.CoarseLowerShape.terminal := of_decide_eq_true (List.all_eq_true.mp ReferenceWeightData.CoarseLowerShape.Assembly.terminals_checked w hw)
  rw [scale_eq] at hc ⊢
  apply checked_global_refined_force_with_error (rate:=(ReferenceActualData.CoarseLowerShape.flowRate:ℝ))
    (s:=ReferenceWeightData.CoarseLowerShape.scale) (multiplier:=multiplier) (k:=1)
    (by norm_num [ReferenceWeightData.CoarseLowerShape.scale]) (by norm_num [multiplier]) (by norm_num)
    ReferenceSensitivityData.CoarseLowerShape.makeCell (fun _=>rfl) c w ((w.cell.flow.segment.right.z-w.start)/500000) hc hl hcell
    ReferenceActualData.CoarseLowerShape.cover_checked hp hr
    (by simp [ReferenceScalarCell.refinementMetadataCheck,ReferenceSensitivityData.CoarseLowerShape.makeCell])
    ReferenceCurveData.CoarseLowerShape.assembly_checked hpiece (List.all_eq_true.mp hpoly parent hp)
    (by norm_num [ReferenceActualData.CoarseLowerShape.flowRate]) (by rw [hstart]; simp only [Rat.cast_div,Rat.cast_sub,Rat.cast_ofNat,ReferenceActualData.CoarseLowerShape.flowRate]; exact le_of_eq (by ring))
    ReferenceAdjointData.CoarseLowerShape.Z_spec.2.2.2.1 hz
    (ReferenceAdjointData.CoarseLowerShape.exponential_contains hw ⟨hz.1.le,hz.2⟩)
  rw [hterm]
  exact ReferenceAdjointData.CoarseLowerShape.terminal_contains
end OptimalG.Certificates.ReferencePositionData.CoarseLowerShape
