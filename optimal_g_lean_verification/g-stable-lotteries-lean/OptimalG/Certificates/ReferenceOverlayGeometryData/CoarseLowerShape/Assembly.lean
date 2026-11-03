import OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Bundle0036_0036
namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Assembly
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [Batch0000.indices,Batch0001.indices,Batch0002.indices,Batch0003.indices,Batch0004.indices,Batch0005.indices,Batch0006.indices,Batch0007.indices,Batch0008.indices,Batch0009.indices,Batch0010.indices,Batch0011.indices,Batch0012.indices,Batch0013.indices,Batch0014.indices,Batch0015.indices,Batch0016.indices,Batch0017.indices,Batch0018.indices,Batch0019.indices,Batch0020.indices,Batch0021.indices,Batch0022.indices,Batch0023.indices,Batch0024.indices,Batch0025.indices,Batch0026.indices,Batch0027.indices,Batch0028.indices,Batch0029.indices,Batch0030.indices,Batch0031.indices,Batch0032.indices,Batch0033.indices,Batch0034.indices,Batch0035.indices,Batch0036.indices].flatten
theorem indices_checked : indices=List.range arrays.cellCount := by decide +kernel
theorem cells_checked : indices.all arrays.cellGeometryCheck=true := by
  simp only [indices,List.all_flatten,List.all_cons,List.all_nil,Batch0000.checked,Batch0001.checked,Batch0002.checked,Batch0003.checked,Batch0004.checked,Batch0005.checked,Batch0006.checked,Batch0007.checked,Batch0008.checked,Batch0009.checked,Batch0010.checked,Batch0011.checked,Batch0012.checked,Batch0013.checked,Batch0014.checked,Batch0015.checked,Batch0016.checked,Batch0017.checked,Batch0018.checked,Batch0019.checked,Batch0020.checked,Batch0021.checked,Batch0022.checked,Batch0023.checked,Batch0024.checked,Batch0025.checked,Batch0026.checked,Batch0027.checked,Batch0028.checked,Batch0029.checked,Batch0030.checked,Batch0031.checked,Batch0032.checked,Batch0033.checked,Batch0034.checked,Batch0035.checked,Batch0036.checked,Bool.true_and]
def frameIndices : List ℕ := [Batch0000.frameIndices,Batch0001.frameIndices,Batch0002.frameIndices,Batch0003.frameIndices,Batch0004.frameIndices,Batch0005.frameIndices,Batch0006.frameIndices,Batch0007.frameIndices,Batch0008.frameIndices,Batch0009.frameIndices,Batch0010.frameIndices,Batch0011.frameIndices,Batch0012.frameIndices,Batch0013.frameIndices,Batch0014.frameIndices,Batch0015.frameIndices,Batch0016.frameIndices,Batch0017.frameIndices,Batch0018.frameIndices,Batch0019.frameIndices,Batch0020.frameIndices,Batch0021.frameIndices,Batch0022.frameIndices,Batch0023.frameIndices,Batch0024.frameIndices,Batch0025.frameIndices,Batch0026.frameIndices,Batch0027.frameIndices,Batch0028.frameIndices,Batch0029.frameIndices,Batch0030.frameIndices,Batch0031.frameIndices,Batch0032.frameIndices,Batch0033.frameIndices,Batch0034.frameIndices,Batch0035.frameIndices,Batch0036.frameIndices].flatten
theorem frame_indices_checked : frameIndices=List.range segments.length := by decide +kernel
theorem r_frames_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by
  simp only [frameIndices,List.all_flatten,List.all_cons,List.all_nil,Batch0000.r_frame_checked,Batch0001.r_frame_checked,Batch0002.r_frame_checked,Batch0003.r_frame_checked,Batch0004.r_frame_checked,Batch0005.r_frame_checked,Batch0006.r_frame_checked,Batch0007.r_frame_checked,Batch0008.r_frame_checked,Batch0009.r_frame_checked,Batch0010.r_frame_checked,Batch0011.r_frame_checked,Batch0012.r_frame_checked,Batch0013.r_frame_checked,Batch0014.r_frame_checked,Batch0015.r_frame_checked,Batch0016.r_frame_checked,Batch0017.r_frame_checked,Batch0018.r_frame_checked,Batch0019.r_frame_checked,Batch0020.r_frame_checked,Batch0021.r_frame_checked,Batch0022.r_frame_checked,Batch0023.r_frame_checked,Batch0024.r_frame_checked,Batch0025.r_frame_checked,Batch0026.r_frame_checked,Batch0027.r_frame_checked,Batch0028.r_frame_checked,Batch0029.r_frame_checked,Batch0030.r_frame_checked,Batch0031.r_frame_checked,Batch0032.r_frame_checked,Batch0033.r_frame_checked,Batch0034.r_frame_checked,Batch0035.r_frame_checked,Batch0036.r_frame_checked,Bool.true_and]
theorem a_frames_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by
  simp only [frameIndices,List.all_flatten,List.all_cons,List.all_nil,Batch0000.a_frame_checked,Batch0001.a_frame_checked,Batch0002.a_frame_checked,Batch0003.a_frame_checked,Batch0004.a_frame_checked,Batch0005.a_frame_checked,Batch0006.a_frame_checked,Batch0007.a_frame_checked,Batch0008.a_frame_checked,Batch0009.a_frame_checked,Batch0010.a_frame_checked,Batch0011.a_frame_checked,Batch0012.a_frame_checked,Batch0013.a_frame_checked,Batch0014.a_frame_checked,Batch0015.a_frame_checked,Batch0016.a_frame_checked,Batch0017.a_frame_checked,Batch0018.a_frame_checked,Batch0019.a_frame_checked,Batch0020.a_frame_checked,Batch0021.a_frame_checked,Batch0022.a_frame_checked,Batch0023.a_frame_checked,Batch0024.a_frame_checked,Batch0025.a_frame_checked,Batch0026.a_frame_checked,Batch0027.a_frame_checked,Batch0028.a_frame_checked,Batch0029.a_frame_checked,Batch0030.a_frame_checked,Batch0031.a_frame_checked,Batch0032.a_frame_checked,Batch0033.a_frame_checked,Batch0034.a_frame_checked,Batch0035.a_frame_checked,Batch0036.a_frame_checked,Bool.true_and]
theorem r_frame_checked : Transport.rankSegmentFrameCheck segments arrays.nodeR (·.r)=true := by
  apply Transport.rankSegmentFrameCheck_of_parts r_frame_size
  intro i hi
  apply List.all_eq_true.mp r_frames_checked i
  rw [frame_indices_checked]
  exact List.mem_range.mpr hi
theorem a_frame_checked : Transport.rankSegmentFrameCheck segments arrays.nodeA (·.a)=true := by
  apply Transport.rankSegmentFrameCheck_of_parts a_frame_size
  intro i hi
  apply List.all_eq_true.mp a_frames_checked i
  rw [frame_indices_checked]
  exact List.mem_range.mpr hi
theorem geometry_checked : arrays.geometryCheck=true := by
  apply Transport.RankOverlayArrays.geometryCheck_of_parts size_checked r_order_checked a_order_checked fine_order_checked
  intro i hi
  apply List.all_eq_true.mp cells_checked i
  rw [indices_checked]
  exact List.mem_range.mpr hi
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Assembly
