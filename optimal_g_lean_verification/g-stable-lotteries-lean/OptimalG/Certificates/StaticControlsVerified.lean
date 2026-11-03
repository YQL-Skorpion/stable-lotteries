import OptimalG.Certificates.StaticResidualData
import OptimalG.Certificates.StaticSupportData
namespace OptimalG.Certificates.StaticCurve
open Set Variational
theorem supported_controls : ∀z∈Icc zStart (1:ℝ),∀v∈controlFeatureSupport staticLowData,
    score z≤featureH staticLow_admissible z (curvePrimitive score z) v :=
  StaticHighData.supported_controls_of_certificates StaticSegmentData.checked
    StaticResidualData.all_checked StaticSupportData.geometry_checked StaticSupportData.numeric_checked
    StaticSupportData.membership_checked StaticSupportData.cover_checked
end OptimalG.Certificates.StaticCurve
