import OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Bundle0032_0035

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0036
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := []
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0036
