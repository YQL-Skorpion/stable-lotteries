import OptimalG.Certificates.ReferenceOverlayData.CoarseLowerShape.Batch0036
import OptimalG.Certificates.ReferenceFluxData.CoarseLowerShape.Assembly
namespace OptimalG.Certificates.ReferenceOverlayData.CoarseLowerShape.Assembly
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cells : List Transport.ReferenceOverlayCell := [Batch0000.cells,Batch0001.cells,Batch0002.cells,Batch0003.cells,Batch0004.cells,Batch0005.cells,Batch0006.cells,Batch0007.cells,Batch0008.cells,Batch0009.cells,Batch0010.cells,Batch0011.cells,Batch0012.cells,Batch0013.cells,Batch0014.cells,Batch0015.cells,Batch0016.cells,Batch0017.cells,Batch0018.cells,Batch0019.cells,Batch0020.cells,Batch0021.cells,Batch0022.cells,Batch0023.cells,Batch0024.cells,Batch0025.cells,Batch0026.cells,Batch0027.cells,Batch0028.cells,Batch0029.cells,Batch0030.cells,Batch0031.cells,Batch0032.cells,Batch0033.cells,Batch0034.cells,Batch0035.cells,Batch0036.cells].flatten
theorem checked : cells.all Transport.ReferenceOverlayCell.check=true := by
  simp only [cells,List.all_flatten,List.all_cons,List.all_nil,Batch0000.checked,Batch0001.checked,Batch0002.checked,Batch0003.checked,Batch0004.checked,Batch0005.checked,Batch0006.checked,Batch0007.checked,Batch0008.checked,Batch0009.checked,Batch0010.checked,Batch0011.checked,Batch0012.checked,Batch0013.checked,Batch0014.checked,Batch0015.checked,Batch0016.checked,Batch0017.checked,Batch0018.checked,Batch0019.checked,Batch0020.checked,Batch0021.checked,Batch0022.checked,Batch0023.checked,Batch0024.checked,Batch0025.checked,Batch0026.checked,Batch0027.checked,Batch0028.checked,Batch0029.checked,Batch0030.checked,Batch0031.checked,Batch0032.checked,Batch0033.checked,Batch0034.checked,Batch0035.checked,Batch0036.checked,Bool.true_and]
theorem positions_linked : cells.map (·.position) = ReferenceFluxData.CoarseLowerShape.Assembly.cells.map (·.position) := by
  simp only [cells,ReferenceFluxData.CoarseLowerShape.Assembly.cells,List.map_flatten,List.map_cons,List.map_nil,Batch0000.positions_linked,Batch0001.positions_linked,Batch0002.positions_linked,Batch0003.positions_linked,Batch0004.positions_linked,Batch0005.positions_linked,Batch0006.positions_linked,Batch0007.positions_linked,Batch0008.positions_linked,Batch0009.positions_linked,Batch0010.positions_linked,Batch0011.positions_linked,Batch0012.positions_linked,Batch0013.positions_linked,Batch0014.positions_linked,Batch0015.positions_linked,Batch0016.positions_linked,Batch0017.positions_linked,Batch0018.positions_linked,Batch0019.positions_linked,Batch0020.positions_linked,Batch0021.positions_linked,Batch0022.positions_linked,Batch0023.positions_linked,Batch0024.positions_linked,Batch0025.positions_linked,Batch0026.positions_linked,Batch0027.positions_linked,Batch0028.positions_linked,Batch0029.positions_linked,Batch0030.positions_linked,Batch0031.positions_linked,Batch0032.positions_linked,Batch0033.positions_linked,Batch0034.positions_linked,Batch0035.positions_linked,Batch0036.positions_linked]
theorem weights_linked : cells.map (·.weight) = ReferenceFluxData.CoarseLowerShape.Assembly.cells.map (·.weight) := by
  simp only [cells,ReferenceFluxData.CoarseLowerShape.Assembly.cells,List.map_flatten,List.map_cons,List.map_nil,Batch0000.weights_linked,Batch0001.weights_linked,Batch0002.weights_linked,Batch0003.weights_linked,Batch0004.weights_linked,Batch0005.weights_linked,Batch0006.weights_linked,Batch0007.weights_linked,Batch0008.weights_linked,Batch0009.weights_linked,Batch0010.weights_linked,Batch0011.weights_linked,Batch0012.weights_linked,Batch0013.weights_linked,Batch0014.weights_linked,Batch0015.weights_linked,Batch0016.weights_linked,Batch0017.weights_linked,Batch0018.weights_linked,Batch0019.weights_linked,Batch0020.weights_linked,Batch0021.weights_linked,Batch0022.weights_linked,Batch0023.weights_linked,Batch0024.weights_linked,Batch0025.weights_linked,Batch0026.weights_linked,Batch0027.weights_linked,Batch0028.weights_linked,Batch0029.weights_linked,Batch0030.weights_linked,Batch0031.weights_linked,Batch0032.weights_linked,Batch0033.weights_linked,Batch0034.weights_linked,Batch0035.weights_linked,Batch0036.weights_linked]
theorem intervals_linked : cells.map (fun c => (c.lo,c.hi)) = ReferenceFluxData.CoarseLowerShape.Assembly.cells.map (fun c => (c.interval.lo,c.interval.hi)) := by
  simp only [cells,ReferenceFluxData.CoarseLowerShape.Assembly.cells,List.map_flatten,List.map_cons,List.map_nil,Batch0000.intervals_linked,Batch0001.intervals_linked,Batch0002.intervals_linked,Batch0003.intervals_linked,Batch0004.intervals_linked,Batch0005.intervals_linked,Batch0006.intervals_linked,Batch0007.intervals_linked,Batch0008.intervals_linked,Batch0009.intervals_linked,Batch0010.intervals_linked,Batch0011.intervals_linked,Batch0012.intervals_linked,Batch0013.intervals_linked,Batch0014.intervals_linked,Batch0015.intervals_linked,Batch0016.intervals_linked,Batch0017.intervals_linked,Batch0018.intervals_linked,Batch0019.intervals_linked,Batch0020.intervals_linked,Batch0021.intervals_linked,Batch0022.intervals_linked,Batch0023.intervals_linked,Batch0024.intervals_linked,Batch0025.intervals_linked,Batch0026.intervals_linked,Batch0027.intervals_linked,Batch0028.intervals_linked,Batch0029.intervals_linked,Batch0030.intervals_linked,Batch0031.intervals_linked,Batch0032.intervals_linked,Batch0033.intervals_linked,Batch0034.intervals_linked,Batch0035.intervals_linked,Batch0036.intervals_linked]
theorem actual_flux_bounds : ∀ c∈ReferenceFluxData.CoarseLowerShape.Assembly.cells,∀ r∈Set.Ioo (c.interval.lo:ℝ) c.interval.hi,
    c.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧ c.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  intro c hc
  unfold ReferenceFluxData.CoarseLowerShape.Assembly.cells at hc
  obtain ⟨bs,hbs,hc⟩ := List.mem_flatten.mp hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hbs
  rcases hbs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Batch0000.actual_flux_bounds c hc
  · exact Batch0001.actual_flux_bounds c hc
  · exact Batch0002.actual_flux_bounds c hc
  · exact Batch0003.actual_flux_bounds c hc
  · exact Batch0004.actual_flux_bounds c hc
  · exact Batch0005.actual_flux_bounds c hc
  · exact Batch0006.actual_flux_bounds c hc
  · exact Batch0007.actual_flux_bounds c hc
  · exact Batch0008.actual_flux_bounds c hc
  · exact Batch0009.actual_flux_bounds c hc
  · exact Batch0010.actual_flux_bounds c hc
  · exact Batch0011.actual_flux_bounds c hc
  · exact Batch0012.actual_flux_bounds c hc
  · exact Batch0013.actual_flux_bounds c hc
  · exact Batch0014.actual_flux_bounds c hc
  · exact Batch0015.actual_flux_bounds c hc
  · exact Batch0016.actual_flux_bounds c hc
  · exact Batch0017.actual_flux_bounds c hc
  · exact Batch0018.actual_flux_bounds c hc
  · exact Batch0019.actual_flux_bounds c hc
  · exact Batch0020.actual_flux_bounds c hc
  · exact Batch0021.actual_flux_bounds c hc
  · exact Batch0022.actual_flux_bounds c hc
  · exact Batch0023.actual_flux_bounds c hc
  · exact Batch0024.actual_flux_bounds c hc
  · exact Batch0025.actual_flux_bounds c hc
  · exact Batch0026.actual_flux_bounds c hc
  · exact Batch0027.actual_flux_bounds c hc
  · exact Batch0028.actual_flux_bounds c hc
  · exact Batch0029.actual_flux_bounds c hc
  · exact Batch0030.actual_flux_bounds c hc
  · exact Batch0031.actual_flux_bounds c hc
  · exact Batch0032.actual_flux_bounds c hc
  · exact Batch0033.actual_flux_bounds c hc
  · exact Batch0034.actual_flux_bounds c hc
  · exact Batch0035.actual_flux_bounds c hc
  · exact Batch0036.actual_flux_bounds c hc
end OptimalG.Certificates.ReferenceOverlayData.CoarseLowerShape.Assembly
