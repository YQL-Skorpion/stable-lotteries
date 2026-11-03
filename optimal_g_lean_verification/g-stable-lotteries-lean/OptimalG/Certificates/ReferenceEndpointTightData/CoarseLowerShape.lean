import OptimalG.Certificates.ReferenceEndpointData.CoarseLowerShape
import OptimalG.Certificates.ExpressionTaylorResidual
namespace OptimalG.Certificates.ReferenceEndpointTightData.CoarseLowerShape
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def certificate : Transport.ReferenceEndpointCertificate := { ReferenceEndpointData.CoarseLowerShape.certificate with
  violation:=⟨584600654932361167281473933086513207862373018,1461501637330902918203684832716283019655932542⟩, firstVariation:=⟨-73075081866545145910184241635814150982796627148,73075081866545145910184241635814150982796627148⟩ }
theorem checked : certificate.check ReferenceEndpointData.CoarseLowerShape.scale 1=true := by decide +kernel
theorem violation_lower : ((1/2500):ℝ)≤(certificate.violation.lo:ℝ)/(ReferenceEndpointData.CoarseLowerShape.scale:ℝ) := by
  norm_num [certificate,ReferenceEndpointData.CoarseLowerShape.scale]
theorem firstVariation_abs : (certificate.firstVariation.maxAbs:ℝ)/(ReferenceEndpointData.CoarseLowerShape.scale:ℝ)≤((1/20):ℝ) := by
  norm_num [certificate,ReferenceEndpointData.CoarseLowerShape.scale,IntegerInterval.maxAbs]
end OptimalG.Certificates.ReferenceEndpointTightData.CoarseLowerShape
