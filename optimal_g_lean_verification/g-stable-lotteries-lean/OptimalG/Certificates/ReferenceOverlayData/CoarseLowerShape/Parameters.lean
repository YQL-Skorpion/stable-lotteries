import OptimalG.Certificates.ReferenceOverlayAssembly
import OptimalG.Certificates.ReferenceOverlayGeometryData.CoarseLowerShape.Assembly
import OptimalG.Certificates.ReferenceDensityData.CoarseLowerShape.Parameters
namespace OptimalG.Certificates.ReferenceOverlayData.CoarseLowerShape
open Transport
noncomputable def force : ℝ→ℝ := Transport.f ReferenceOverlayGeometryData.CoarseLowerShape.segments (fun _=>ReferencePositionData.CoarseLowerShape.force 1) (fun _=>ReferencePositionData.CoarseLowerShape.force 2)
noncomputable def weight : ℝ→ℝ := Transport.W ReferenceOverlayGeometryData.CoarseLowerShape.segments (fun _ z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z) (fun _ z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
end OptimalG.Certificates.ReferenceOverlayData.CoarseLowerShape
