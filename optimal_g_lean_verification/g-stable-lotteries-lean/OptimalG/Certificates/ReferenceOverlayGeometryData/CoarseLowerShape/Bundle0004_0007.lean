import OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Bundle0000_0003

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0004
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159]
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0004

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0005
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191]
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0005

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0006
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223]
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0006

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255]
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0007
