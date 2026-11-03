import OptimalG.Certificates.StaticBinaryHighInputs
import OptimalG.Certificates.StaticBinaryAssembly
import OptimalG.Certificates.StaticBinarySmallIntervals
import OptimalG.Certificates.StaticBinaryStationaryIntervals
import OptimalG.Certificates.StaticBinaryLateIntervals

namespace OptimalG.Certificates.StaticCurve
open Set Variational StaticBinaryCentralExpressions

/-- The actual static curve satisfies every binary inequality, given the
separate finite certificate for all its supported high controls. -/
theorem binary_of_supported_controls
    (hcontrols : ∀ z∈Icc zStart 1,∀v∈controlFeatureSupport staticLowData,
      score z≤featureH staticLow_admissible z (curvePrimitive score z) v) :
    ∀ p∈Ioo (0:ℝ) 1,∀ q∈Icc (0:ℝ) p,normalizedBinaryTest score p q≤L := by
  have hg : BinaryCurveGeometry score L S slope c := by
    simpa only [StaticBinaryInputs.slope,L,S,c] using binaryGeometry
  have hs := static_binary_small_intervals verifierCurve hg
  rw [StaticBinaryInputs.initial] at hs
  exact StaticBinaryAssembly.binary
    (fun p hp q hq => StaticBinaryInputs.terminal_bound hp hq)
    (fun p hp => StaticBinaryInputs.early_deficit hp)
    (StaticBinaryInputs.fixed_cap_control hcontrols) hs
    static_binary_stationary_intervals static_binary_late_intervals

end OptimalG.Certificates.StaticCurve
