import OptimalG.LineControlFeature
import OptimalG.BinaryCurveGeometry

/-! The fixed line control is obtained from the completed curve's actual
essential score graph. No additional finite certificate is used here. -/
namespace OptimalG
open Set

namespace Variational

/-- Specialize the actual all-feature inequality to the diagonal control
at rank .36. Its support membership and primitive value follow from the
completed curve's graph and line geometry. -/
theorem completed_curve_fixed_line_control {phi : ℝ → ℝ} {lam slope c : ℝ}
    {d : LowRankData} (hd : Admissible lam d)
    (g : BinaryCurveGeometry phi lam d.S slope c)
    (hgraph : ∀ r ∈ Icc xLo xHi, (r,phi r) ∈ rankScoreSupport d.phi)
    (hprimitive : ∀ r ∈ Icc (527/2000 : ℝ) xHi,
      curvePrimitive phi r = primitive lam d r)
    (hcontrol : ∀ r ∈ Icc zStart 1, ∀ v ∈ controlFeatureSupport d,
      phi r ≤ featureH hd r (curvePrimitive phi r) v) :
    ∀ r ∈ Icc (391/500 : ℝ) 1, phi r ≤
      -Certificates.LineControl.theta lam d.S*(r-lam)-
        Certificates.LineControl.alpha lam d.S*
          (quadratic lam (r-9/25)-d.S-curvePrimitive phi r) := by
  have hline := g.line_score (9/25) ⟨by norm_num,by norm_num⟩
  have hmember := hgraph (9/25) ⟨by norm_num [xLo],by norm_num [xHi]⟩
  rw [hline] at hmember
  have hR : primitive lam d (9/25) = quadratic lam (9/25)-d.S := by
    rw [←hprimitive (9/25) ⟨by norm_num,by norm_num [xHi]⟩]
    exact g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩
  exact lineControl_bound_of_all_features hd hmember hR hcontrol

end Variational
end OptimalG
