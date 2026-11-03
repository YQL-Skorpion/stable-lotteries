import OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Bundle0012_0015

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0016
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := [512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543]
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0016

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0017
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := [544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575]
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0017

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0018
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := [576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607]
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0018

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0019
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := [608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639]
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0019
