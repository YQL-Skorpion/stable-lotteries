import OptimalG.VariationalFeatureBounds

/-! Active support controls give exact affine supporting inequalities. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

theorem active_feature_supports_x {lam z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u)
    (huHigh : u ≤ quadratic lam z-d.S)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hactive : featureH hd z u v = vectorField lam d z u)
    {w : ℝ × ℝ} (hw : w ∈ rankScoreSupport d.phi) :
    w.2+featureTheta lam d v*w.1 ≤ v.2.1+featureTheta lam d v*v.1.2.1 := by
  have hc := (hd.controlFeatureSupport_subset hv).1
  have hnew := hd.feature_mem_support_of_rankScores hc.1 hw (hd.featureSupport_rankScores hv).2
    ((le_max_right _ _).trans hc.2.2.1)
  have hn := (hd.controlFeatureSupport_subset hnew).1
  have hle : featureH hd z u v ≤ featureH hd z u ((v.1.1,w.1,v.1.2.2),w.2,v.2.2) := by
    rw [hactive]
    exact (min_le_right _ _).trans (hd.essInf_le_featureH z u hnew)
  rw [featureH_eq_value hd z u v.2.1 v.2.2 hc,
    featureH_eq_value hd z u w.2 v.2.2 hn] at hle
  have hD : 0 < Certificates.Control.det (2*lam-v.1.2.1) (v.1.1+v.1.2.2-lam)
      (primitive lam d v.1.1) (quadratic lam (1-v.1.1)-d.S) := by
    change 0 < controlDeterminant lam d v.1
    linarith [hd.determinant_positive hc]
  have hD' : 0 < Certificates.Control.det ((2*lam-v.1.2.1)-(w.1-v.1.2.1)) (v.1.1+v.1.2.2-lam)
      (primitive lam d v.1.1) (quadratic lam (1-v.1.1)-d.S) := by
    have he : (2*lam-v.1.2.1)-(w.1-v.1.2.1) = 2*lam-w.1 := by ring
    rw [he]
    change 0 < controlDeterminant lam d (v.1.1,w.1,v.1.2.2)
    linarith [hd.determinant_positive hn]
  have hcx : 0 < Certificates.Control.cx (z-lam) (v.1.1+v.1.2.2-lam)
      (primitive lam d v.1.1) (quadratic lam (z-v.1.1)-d.S-u) := by
    linarith [(hd.control_coefficients_positive hc hz huLow huHigh).1]
  have hh := Certificates.Control.value_x_shift_order_iff (z-lam) (2*lam-v.1.2.1)
    (v.1.1+v.1.2.2-lam) (primitive lam d v.1.1) (quadratic lam (1-v.1.1)-d.S)
    (quadratic lam (z-v.1.1)-d.S-u) v.2.1 v.2.2 (w.1-v.1.2.1) (w.2-v.2.1) hD hD' hcx
  have he : (2*lam-v.1.2.1)-(w.1-v.1.2.1) = 2*lam-w.1 := by ring
  rw [he,add_sub_cancel] at hh
  have hscore := hh.mp hle
  change w.2-v.2.1+featureTheta lam d v*(w.1-v.1.2.1) ≤ 0 at hscore
  nlinarith

theorem active_feature_supports_y {lam z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u)
    (huHigh : u ≤ quadratic lam z-d.S)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hactive : featureH hd z u v = vectorField lam d z u)
    {w : ℝ × ℝ} (hw : w ∈ rankScoreSupport d.phi) (hpw : v.1.1 ≤ w.1) :
    w.2+featureTheta lam d v*w.1 ≤ v.2.2+featureTheta lam d v*v.1.2.2 := by
  have hc := (hd.controlFeatureSupport_subset hv).1
  have hnew := hd.feature_mem_support_of_rankScores hc.1 (hd.featureSupport_rankScores hv).1 hw hpw
  have hn := (hd.controlFeatureSupport_subset hnew).1
  have hle : featureH hd z u v ≤ featureH hd z u ((v.1.1,v.1.2.1,w.1),v.2.1,w.2) := by
    rw [hactive]
    exact (min_le_right _ _).trans (hd.essInf_le_featureH z u hnew)
  rw [featureH_eq_value hd z u v.2.1 v.2.2 hc,
    featureH_eq_value hd z u v.2.1 w.2 hn] at hle
  have hD : 0 < Certificates.Control.det (2*lam-v.1.2.1) (v.1.1+v.1.2.2-lam)
      (primitive lam d v.1.1) (quadratic lam (1-v.1.1)-d.S) := by
    change 0 < controlDeterminant lam d v.1
    linarith [hd.determinant_positive hc]
  have hD' : 0 < Certificates.Control.det (2*lam-v.1.2.1) ((v.1.1+v.1.2.2-lam)+(w.1-v.1.2.2))
      (primitive lam d v.1.1) (quadratic lam (1-v.1.1)-d.S) := by
    have he : (v.1.1+v.1.2.2-lam)+(w.1-v.1.2.2) = v.1.1+w.1-lam := by ring
    rw [he]
    change 0 < controlDeterminant lam d (v.1.1,v.1.2.1,w.1)
    linarith [hd.determinant_positive hn]
  have hcy : 0 < Certificates.Control.cy (z-lam) (2*lam-v.1.2.1)
      (quadratic lam (1-v.1.1)-d.S) (quadratic lam (z-v.1.1)-d.S-u) := by
    linarith [(hd.control_coefficients_positive hc hz huLow huHigh).2]
  have hh := Certificates.Control.value_y_shift_order_iff (z-lam) (2*lam-v.1.2.1)
    (v.1.1+v.1.2.2-lam) (primitive lam d v.1.1) (quadratic lam (1-v.1.1)-d.S)
    (quadratic lam (z-v.1.1)-d.S-u) v.2.1 v.2.2 (w.1-v.1.2.2) (w.2-v.2.2) hD hD' hcy
  have he : (v.1.1+v.1.2.2-lam)+(w.1-v.1.2.2) = v.1.1+w.1-lam := by ring
  rw [he,add_sub_cancel] at hh
  have hscore := hh.mp hle
  change w.2-v.2.2+featureTheta lam d v*(w.1-v.1.2.2) ≤ 0 at hscore
  nlinarith

end OptimalG.Variational
