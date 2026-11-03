import OptimalG.Certificates.ReferenceLowCurve
import OptimalG.Certificates.TransportReferenceData.CoarseLowerShape
namespace OptimalG.Certificates.ReferenceLowData.CoarseLowerShape
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked : TransportReferenceData.CoarseLowerShape.data.lowCurveCheck=true := by decide +kernel
theorem derivative (r : ℝ) : HasDerivAt TransportReferenceData.CoarseLowerShape.data.lowPrimitive (TransportReferenceData.CoarseLowerShape.data.lowScore r) r :=
  TransportReferenceData.CoarseLowerShape.data.lowPrimitive_hasDerivAt checked r
theorem continuous_score : Continuous TransportReferenceData.CoarseLowerShape.data.lowScore := TransportReferenceData.CoarseLowerShape.data.lowScore_continuous checked
end OptimalG.Certificates.ReferenceLowData.CoarseLowerShape
