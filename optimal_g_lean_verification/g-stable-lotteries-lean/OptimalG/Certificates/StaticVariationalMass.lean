import OptimalG.Certificates.StaticCurveMassFacts
import OptimalG.CompletedVariationalMass

namespace OptimalG.Certificates.StaticCurve
open Set Variational

theorem variational_mass
    (hcontrol : ∀ r∈Icc zStart 1,∀ v∈controlFeatureSupport staticLowData,
      score r≤featureH staticLow_admissible r (curvePrimitive score r) v)
    {p : ℝ} (hp : p∈Icc (527/2000:ℝ) (9/25)) :
    ∃ beta eta,ThreeFunctionTest score StaticLow.lam p beta eta :=
  completed_curve_variational_mass staticLow_admissible verifierCurve binaryGeometry
    StaticMass.parameter_ranges.2 hp initial_formula line_782
    (fun _ hr => score_graph hr) (fun _ hr => primitive_variational hr) hcontrol

end OptimalG.Certificates.StaticCurve
