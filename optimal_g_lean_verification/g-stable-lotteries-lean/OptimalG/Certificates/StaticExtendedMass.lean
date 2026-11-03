import OptimalG.Certificates.StaticCurveMassFacts
import OptimalG.StaticExtendedMassVerification
import OptimalG.CompletedBaseSupport

namespace OptimalG.Certificates.StaticCurve
open Set Variational

theorem extended_mass
    (hcontrol : ∀ r∈Icc zStart 1,∀ v∈controlFeatureSupport staticLowData,
      score r≤featureH staticLow_admissible r (curvePrimitive score r) v)
    {p : ℝ} (hp : p∈Icc (9/25:ℝ) StaticLow.lam) :
    ∃ beta eta,ThreeFunctionTest score StaticLow.lam p beta eta := by
  obtain ⟨t,beta0,eta0,ht,hbeta0,heta0,hfirst,hsecond,hsupport,hbase⟩ :=
    completed_curve_base_support staticLow_admissible verifierCurve mass_geometry
      StaticMass.parameter_ranges.2 (fun _ hr => score_graph hr)
      (fun _ hr => primitive_variational hr) hcontrol
  exact ⟨_,_,verifierCurve.static_extended_mass_verified mass_geometry
    StaticMass.parameter_ranges.2 hp ht initial_formula line_782
    hfirst hsecond hsupport hbase StaticMass.anchor_bounds.1.1
    (by constructor <;> linarith only [StaticMass.anchor_bounds.2.1,StaticMass.anchor_bounds.2.2])
    (fun _ hr => tail_anchor_score hr) (fun _ hr => tail_anchor_primitive hr)
    StaticMass.backward_bounds.1.1
    ⟨by linarith only [StaticMass.backward_bounds.2.1],StaticMass.backward_bounds.2.2⟩⟩

end OptimalG.Certificates.StaticCurve
