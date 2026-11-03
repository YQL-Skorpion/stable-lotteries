import OptimalG.VariationalThetaUpper
import OptimalG.VariationalTerminalSlope

/-! The uniform terminal control derivative bound is obtained from the
actual essential score support, including boundary controls. -/
namespace OptimalG.Variational
open Set

theorem Admissible.featureAlpha_lt_453 {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {v : ControlFeature} (hv : v∈controlFeatureSupport d) :
    featureAlpha lam d v<(4.53:ℝ) := by
  have hc := (hd.controlFeatureSupport_subset hv).1
  have hA := hd.rankScoreSupport_bounds (hd.featureSupport_rankScores hv).1
  have hB := hd.rankScoreSupport_bounds (hd.featureSupport_rankScores hv).2
  apply Certificates.Control.alpha_lt lam v.1.1 v.1.2.1 v.1.2.2
    (primitive lam d v.1.1) (quadratic lam (1-v.1.1)-d.S) v.2.1 v.2.2
    hd.compact_lambdaRange
  · convert! hc.1 using 1 <;> norm_num [pLo,pHi]
  · convert! hA.1 using 1 <;> norm_num [xLo,xHi]
  · convert! hB.1 using 1 <;> norm_num [xLo,xHi]
  · exact (le_max_right _ _).trans hc.2.2.1
  · exact hA.2.1
  · exact hA.2.2
  · exact hB.2.1
  · exact hB.2.2
  · exact hd.determinant_sharp hc

theorem terminal_control_slope_lower {lam b H : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hS : d.S≤(0.023354:ℝ))
    {v : ControlFeature} (hv : v∈controlFeatureSupport d) (hline : H≤lam-b) :
    -0.78+4.53*(H+b-lam-0.36)≤
      -featureTheta lam d v+featureAlpha lam d v*(b-lam-v.1.1+H) := by
  have htheta := hd.featureTheta_lt_78 hS hv
  have halpha := hd.featureAlpha_lt_453 hv
  have hdom := (hd.controlFeatureSupport_subset hv).1
  have hp : v.1.1∈Icc (0.25:ℝ) 0.36 := by
    convert! hdom.1 using 1 <;> norm_num [pLo,pHi]
  have hm := mul_le_mul_of_nonpos_right halpha.le
    (show b-lam-v.1.1+H≤0 by linarith only [hline,hp.1])
  nlinarith only [hm,htheta,hp.2]

end OptimalG.Variational
