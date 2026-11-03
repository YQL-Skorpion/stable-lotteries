import OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Bundle0004_0007

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0008
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := [256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287]
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0008

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0009
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := [288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319]
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0009

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0010
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := [320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351]
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0010

namespace OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0011
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def indices : List ℕ := [352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383]
theorem checked : indices.all arrays.cellGeometryCheck=true := by decide +kernel
def frameIndices : List ℕ := [352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383]
theorem r_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeR (·.r))=true := by decide +kernel
theorem a_frame_checked : frameIndices.all (Transport.rankSegmentFrameCellCheck segments arrays.nodeA (·.a))=true := by decide +kernel
end OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Batch0011
