import OptimalG.Certificates.ReferenceDensityAssembly
import OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Parameters
namespace OptimalG.Certificates.ReferenceDensityData.CoarseLowerShape
open Set Transport
def scale : ℕ := 1208925819614629174706176
noncomputable def force (c : ReferenceDensityCell) : ℝ→ℝ := segmentDensity c.segment c.rank (if c.useR then ReferencePositionData.CoarseLowerShape.force 1 else ReferencePositionData.CoarseLowerShape.force 2)
noncomputable def weight (c : ReferenceDensityCell) : ℝ→ℝ := segmentDensity c.segment c.rank (if c.useR then (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z) else (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z))
end OptimalG.Certificates.ReferenceDensityData.CoarseLowerShape
