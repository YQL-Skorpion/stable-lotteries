import OptimalG.Certificates.ReferenceEndpointLink
import OptimalG.Certificates.ReferenceEndpointData.CoarseLowerShape
import OptimalG.Certificates.ReferenceCurveData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityCurveData.CoarseLowerShape
namespace OptimalG.Certificates.ReferenceEndpointLinkData.CoarseLowerShape
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def start : ℚ := (7835342428237777/10000000000000000)
def finish : ℚ := (8624179577667147/10000000000000000)
theorem X_endpoint_checked : IntegerInterval.centerRadiusCheck ReferenceEndpointData.CoarseLowerShape.scale (ReferenceCurveData.CoarseLowerShape.piece347.primitiveQ ReferenceCurveData.CoarseLowerShape.piece347.length) (78883714942937/500000000000000000000) ReferenceEndpointData.CoarseLowerShape.certificate.flowDeficit=true := by decide +kernel
theorem X_last_geometry : ReferenceCurveData.CoarseLowerShape.piece347.lo<ReferenceCurveData.CoarseLowerShape.piece347.hi ∧ ReferenceCurveData.CoarseLowerShape.piece347.hi=finish := by decide +kernel
theorem X_last_member : ReferenceCurveData.CoarseLowerShape.piece347∈ReferenceCurveData.CoarseLowerShape.pieces := by simp only [ReferenceCurveData.CoarseLowerShape.pieces,List.mem_cons,List.mem_singleton]; tauto
theorem V_endpoint_checked : IntegerInterval.centerRadiusCheck ReferenceEndpointData.CoarseLowerShape.scale (ReferenceSensitivityCurveData.CoarseLowerShape.piece347.primitiveQ ReferenceSensitivityCurveData.CoarseLowerShape.piece347.length) (203431927840541042145166185969/250000000000000000000000000000000) ReferenceEndpointData.CoarseLowerShape.certificate.flowVariation=true := by decide +kernel
theorem V_last_geometry : ReferenceSensitivityCurveData.CoarseLowerShape.piece347.lo<ReferenceSensitivityCurveData.CoarseLowerShape.piece347.hi ∧ ReferenceSensitivityCurveData.CoarseLowerShape.piece347.hi=finish := by decide +kernel
theorem V_last_member : ReferenceSensitivityCurveData.CoarseLowerShape.piece347∈ReferenceSensitivityCurveData.CoarseLowerShape.pieces := by simp only [ReferenceSensitivityCurveData.CoarseLowerShape.pieces,List.mem_cons,List.mem_singleton]; tauto
end OptimalG.Certificates.ReferenceEndpointLinkData.CoarseLowerShape
