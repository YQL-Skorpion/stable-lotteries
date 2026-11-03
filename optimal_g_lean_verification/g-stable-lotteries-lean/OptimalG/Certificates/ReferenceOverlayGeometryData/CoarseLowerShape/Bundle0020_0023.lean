import OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Bundle0016_0019

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0020
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := [640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671]
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0020

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0021
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := [672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695]
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0021

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0022
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := []
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0022

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0023
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := []
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0023
