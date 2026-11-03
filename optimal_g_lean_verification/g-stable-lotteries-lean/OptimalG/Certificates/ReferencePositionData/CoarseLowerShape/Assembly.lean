import OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Bundle0083_0086
namespace OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Assembly
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cells : List Transport.ReferencePositionCell := [Batch0000.cells,Batch0001.cells,Batch0002.cells,Batch0003.cells,Batch0004.cells,Batch0005.cells,Batch0006.cells,Batch0007.cells,Batch0008.cells,Batch0009.cells,Batch0010.cells,Batch0011.cells,Batch0012.cells,Batch0013.cells,Batch0014.cells,Batch0015.cells,Batch0016.cells,Batch0017.cells,Batch0018.cells,Batch0019.cells,Batch0020.cells,Batch0021.cells,Batch0022.cells,Batch0023.cells,Batch0024.cells,Batch0025.cells,Batch0026.cells,Batch0027.cells,Batch0028.cells,Batch0029.cells,Batch0030.cells,Batch0031.cells,Batch0032.cells,Batch0033.cells,Batch0034.cells,Batch0035.cells,Batch0036.cells,Batch0037.cells,Batch0038.cells,Batch0039.cells,Batch0040.cells,Batch0041.cells,Batch0042.cells,Batch0043.cells,Batch0044.cells,Batch0045.cells,Batch0046.cells,Batch0047.cells,Batch0048.cells,Batch0049.cells,Batch0050.cells,Batch0051.cells,Batch0052.cells,Batch0053.cells,Batch0054.cells,Batch0055.cells,Batch0056.cells,Batch0057.cells,Batch0058.cells,Batch0059.cells,Batch0060.cells,Batch0061.cells,Batch0062.cells,Batch0063.cells,Batch0064.cells,Batch0065.cells,Batch0066.cells,Batch0067.cells,Batch0068.cells,Batch0069.cells,Batch0070.cells,Batch0071.cells,Batch0072.cells,Batch0073.cells,Batch0074.cells,Batch0075.cells,Batch0076.cells,Batch0077.cells,Batch0078.cells,Batch0079.cells,Batch0080.cells,Batch0081.cells,Batch0082.cells,Batch0083.cells,Batch0084.cells,Batch0085.cells,Batch0086.cells].flatten
theorem checked : cells.all (fun c => c.check scale 1)=true := by
  simp only [cells,List.all_flatten,List.all_cons,List.all_nil,Batch0000.checked,Batch0001.checked,Batch0002.checked,Batch0003.checked,Batch0004.checked,Batch0005.checked,Batch0006.checked,Batch0007.checked,Batch0008.checked,Batch0009.checked,Batch0010.checked,Batch0011.checked,Batch0012.checked,Batch0013.checked,Batch0014.checked,Batch0015.checked,Batch0016.checked,Batch0017.checked,Batch0018.checked,Batch0019.checked,Batch0020.checked,Batch0021.checked,Batch0022.checked,Batch0023.checked,Batch0024.checked,Batch0025.checked,Batch0026.checked,Batch0027.checked,Batch0028.checked,Batch0029.checked,Batch0030.checked,Batch0031.checked,Batch0032.checked,Batch0033.checked,Batch0034.checked,Batch0035.checked,Batch0036.checked,Batch0037.checked,Batch0038.checked,Batch0039.checked,Batch0040.checked,Batch0041.checked,Batch0042.checked,Batch0043.checked,Batch0044.checked,Batch0045.checked,Batch0046.checked,Batch0047.checked,Batch0048.checked,Batch0049.checked,Batch0050.checked,Batch0051.checked,Batch0052.checked,Batch0053.checked,Batch0054.checked,Batch0055.checked,Batch0056.checked,Batch0057.checked,Batch0058.checked,Batch0059.checked,Batch0060.checked,Batch0061.checked,Batch0062.checked,Batch0063.checked,Batch0064.checked,Batch0065.checked,Batch0066.checked,Batch0067.checked,Batch0068.checked,Batch0069.checked,Batch0070.checked,Batch0071.checked,Batch0072.checked,Batch0073.checked,Batch0074.checked,Batch0075.checked,Batch0076.checked,Batch0077.checked,Batch0078.checked,Batch0079.checked,Batch0080.checked,Batch0081.checked,Batch0082.checked,Batch0083.checked,Batch0084.checked,Batch0085.checked,Batch0086.checked,Bool.true_and]
theorem actual_bounds : ∀ w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates,∀ z∈Set.Ioc (w.cell.flow.segment.left.z:ℝ) w.cell.flow.segment.right.z,
    |force 1 z|≤100 ∧ |force 2 z|≤100 := by
  intro w hw
  obtain ⟨batch,hbatch,hw⟩ := List.mem_flatten.mp hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hbatch
  rcases hbatch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Batch0000.actual_bounds w hw
  · exact Batch0001.actual_bounds w hw
  · exact Batch0002.actual_bounds w hw
  · exact Batch0003.actual_bounds w hw
  · exact Batch0004.actual_bounds w hw
  · exact Batch0005.actual_bounds w hw
  · exact Batch0006.actual_bounds w hw
  · exact Batch0007.actual_bounds w hw
  · exact Batch0008.actual_bounds w hw
  · exact Batch0009.actual_bounds w hw
  · exact Batch0010.actual_bounds w hw
  · exact Batch0011.actual_bounds w hw
  · exact Batch0012.actual_bounds w hw
  · exact Batch0013.actual_bounds w hw
  · exact Batch0014.actual_bounds w hw
  · exact Batch0015.actual_bounds w hw
  · exact Batch0016.actual_bounds w hw
  · exact Batch0017.actual_bounds w hw
  · exact Batch0018.actual_bounds w hw
  · exact Batch0019.actual_bounds w hw
  · exact Batch0020.actual_bounds w hw
  · exact Batch0021.actual_bounds w hw
  · exact Batch0022.actual_bounds w hw
  · exact Batch0023.actual_bounds w hw
  · exact Batch0024.actual_bounds w hw
  · exact Batch0025.actual_bounds w hw
  · exact Batch0026.actual_bounds w hw
  · exact Batch0027.actual_bounds w hw
  · exact Batch0028.actual_bounds w hw
  · exact Batch0029.actual_bounds w hw
  · exact Batch0030.actual_bounds w hw
  · exact Batch0031.actual_bounds w hw
  · exact Batch0032.actual_bounds w hw
  · exact Batch0033.actual_bounds w hw
  · exact Batch0034.actual_bounds w hw
  · exact Batch0035.actual_bounds w hw
  · exact Batch0036.actual_bounds w hw
  · exact Batch0037.actual_bounds w hw
  · exact Batch0038.actual_bounds w hw
  · exact Batch0039.actual_bounds w hw
  · exact Batch0040.actual_bounds w hw
  · exact Batch0041.actual_bounds w hw
  · exact Batch0042.actual_bounds w hw
  · exact Batch0043.actual_bounds w hw
  · exact Batch0044.actual_bounds w hw
  · exact Batch0045.actual_bounds w hw
  · exact Batch0046.actual_bounds w hw
  · exact Batch0047.actual_bounds w hw
  · exact Batch0048.actual_bounds w hw
  · exact Batch0049.actual_bounds w hw
  · exact Batch0050.actual_bounds w hw
  · exact Batch0051.actual_bounds w hw
  · exact Batch0052.actual_bounds w hw
  · exact Batch0053.actual_bounds w hw
  · exact Batch0054.actual_bounds w hw
  · exact Batch0055.actual_bounds w hw
  · exact Batch0056.actual_bounds w hw
  · exact Batch0057.actual_bounds w hw
  · exact Batch0058.actual_bounds w hw
  · exact Batch0059.actual_bounds w hw
  · exact Batch0060.actual_bounds w hw
  · exact Batch0061.actual_bounds w hw
  · exact Batch0062.actual_bounds w hw
  · exact Batch0063.actual_bounds w hw
  · exact Batch0064.actual_bounds w hw
  · exact Batch0065.actual_bounds w hw
  · exact Batch0066.actual_bounds w hw
  · exact Batch0067.actual_bounds w hw
  · exact Batch0068.actual_bounds w hw
  · exact Batch0069.actual_bounds w hw
  · exact Batch0070.actual_bounds w hw
  · exact Batch0071.actual_bounds w hw
  · exact Batch0072.actual_bounds w hw
  · exact Batch0073.actual_bounds w hw
  · exact Batch0074.actual_bounds w hw
  · exact Batch0075.actual_bounds w hw
  · exact Batch0076.actual_bounds w hw
  · exact Batch0077.actual_bounds w hw
  · exact Batch0078.actual_bounds w hw
  · exact Batch0079.actual_bounds w hw
  · exact Batch0080.actual_bounds w hw
  · exact Batch0081.actual_bounds w hw
  · exact Batch0082.actual_bounds w hw
  · exact Batch0083.actual_bounds w hw
  · exact Batch0084.actual_bounds w hw
  · exact Batch0085.actual_bounds w hw
  · exact Batch0086.actual_bounds w hw
theorem global_bounds {z : ℝ}
    (hz : z∈Set.Ioc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish) :
    |force 1 z|≤100 ∧ |force 2 z|≤100 := by
  obtain ⟨flow,hflow,_,hzflow,_⟩ := Transport.referenceField_selected Transport.ReferenceFlowCell.actualAlpha ReferenceWeightData.CoarseLowerShape.Assembly.cover_checked hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hflow
  exact actual_bounds w hw z hzflow
end OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Assembly
