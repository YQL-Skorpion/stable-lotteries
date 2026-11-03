import OptimalG.Certificates.StaticCurveMassFacts
import OptimalG.StaticCompletedHighMass
import OptimalG.CompletedLineControl

namespace OptimalG.Certificates.StaticCurve
open Set Variational

theorem high_mass
    (hcontrol : ∀ r∈Icc zStart 1,∀ v∈controlFeatureSupport staticLowData,
      score r≤featureH staticLow_admissible r (curvePrimitive score r) v)
    (hbinary : ∀ p∈Ioo (StaticLow.lam:ℝ) 1,∀ q∈Icc (0:ℝ) StaticLow.lam,
      q+(p/curvePrimitive score p)*packingDelta score p q≤StaticLow.lam) :
    VerifierOn (Ioo (StaticLow.lam:ℝ) 1) score StaticLow.lam
      (fun p=>p/curvePrimitive score p) (highMassCorrection score StaticLow.lam) := by
  have hd := line_deficits (r:=(7/20:ℝ)) ⟨by
    norm_num [StaticLow.rightContact,UpperProfileData.rightContact],by norm_num [StaticHigh.departure]⟩
  have hc := completed_curve_fixed_line_control staticLow_admissible binaryGeometry
    (fun _ hr=>score_graph hr) (fun _ hr=>primitive_variational hr) hcontrol
  exact verifierCurve.static_completed_curve_high_mass mass_geometry
    StaticMass.parameter_ranges.2 concave line_782
    (by rw [hd.1]; norm_num) (by rw [hd.2]; norm_num)
    StaticMass.anchor_bounds.1 StaticMass.anchor_bounds.2
    StaticMass.backward_bounds.1 StaticMass.backward_bounds.2
    (fun _ hr=>tail_anchor_score hr) (fun _ hr=>tail_anchor_primitive hr) hbinary hc

end OptimalG.Certificates.StaticCurve
