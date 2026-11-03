import OptimalG.Certificates.ReferenceRankCropCheck
import OptimalG.Certificates.ReferenceWeightTolerance
import OptimalG.Certificates.ReferenceWeightPositivity
import OptimalG.Certificates.ReferenceRefinement
import OptimalG.Certificates.ReferenceActualData.CoarseLowerShape
import OptimalG.Certificates.ReferenceEndpointLinkData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Assembly
import OptimalG.Certificates.TransportReferenceData.CoarseLowerShape
namespace OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def scale : ℕ := 1208925819614629174706176
def multiplier : ℕ := 1208925819614629174706176
def terminal : IntegerInterval := ⟨28799302986694716841432,28799684444933683388968⟩
theorem terminal_checked : IntegerInterval.centerRadiusCheck scale (ReferenceCurveData.CoarseLowerShape.piece347.primitiveQ ReferenceCurveData.CoarseLowerShape.piece347.length) ((ReferenceActualData.CoarseLowerShape.finish-ReferenceActualData.CoarseLowerShape.start)/500000) terminal=true := by decide +kernel
end OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape
