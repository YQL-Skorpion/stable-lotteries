import OptimalG.Certificates.TransportReferenceData.CoarseLowerShape
import OptimalG.Certificates.ReferenceScalarTolerances
namespace OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def scale : ℕ := 1208925819614629174706176
def flowResidual : ℤ := ((scale/1000000:ℕ):ℤ)
def auxiliaryResidual : ℤ := ((scale/200:ℕ):ℤ)
def makeCell (flow : Transport.ReferenceFlowCell) : Transport.ReferenceScalarCell :=
  ⟨flow,TransportReferenceData.CoarseLowerShape.leftContact,TransportReferenceData.CoarseLowerShape.rightContact,
    (7835342428237777/10000000000000000),(8624179577667147/10000000000000000),TransportReferenceData.CoarseLowerShape.gauge,
    TransportReferenceData.CoarseLowerShape.gaugeDerivative⟩
end OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape
