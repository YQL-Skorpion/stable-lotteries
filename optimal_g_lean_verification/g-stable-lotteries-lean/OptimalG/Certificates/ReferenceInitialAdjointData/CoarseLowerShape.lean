import OptimalG.Certificates.ReferenceCurveData.CoarseLowerShape
namespace OptimalG.Certificates.ReferenceInitialAdjointData.CoarseLowerShape
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def initial : ℚ := (272412348566904586561649901729/200000000000000000000000000000000)
theorem initial_linked : initial=ReferenceCurveData.CoarseLowerShape.piece0.f0 := by decide +kernel
end OptimalG.Certificates.ReferenceInitialAdjointData.CoarseLowerShape
