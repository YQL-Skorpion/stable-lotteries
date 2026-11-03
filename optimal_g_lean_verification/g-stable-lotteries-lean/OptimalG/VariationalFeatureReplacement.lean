import OptimalG.VariationalCapAlgebra

/-! Exact pointwise rank replacements for arbitrary bounded score features. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem Admissible.feature_x_replacement {lam z u A B : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {c : Control} (hc : c ∈ controlDomain)
    (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    {w : ℝ × ℝ} (hw : w.1 ∈ Icc xLo xHi)
    (hs : A+featureTheta lam d (c,A,B)*c.2.1 ≤ w.2+featureTheta lam d (c,A,B)*w.1) :
    featureH hd z u ((c.1,w.1,c.2.2),w.2,B) ≤ featureH hd z u (c,A,B) ∧
    featureTheta lam d (c,A,B) ≤ featureTheta lam d ((c.1,w.1,c.2.2),w.2,B) := by
  have hc' : (c.1,w.1,c.2.2) ∈ controlDomain := ⟨hc.1,hw,hc.2.2⟩
  have he : (2*lam-c.2.1)-(w.1-c.2.1) = 2*lam-w.1 := by ring
  have hD : 0 < Certificates.Control.det (2*lam-c.2.1) (c.1+c.2.2-lam)
      (primitive lam d c.1) (quadratic lam (1-c.1)-d.S) := by
    change 0 < controlDeterminant lam d c
    linarith [hd.determinant_positive hc]
  have hD' : 0 < Certificates.Control.det ((2*lam-c.2.1)-(w.1-c.2.1)) (c.1+c.2.2-lam)
      (primitive lam d c.1) (quadratic lam (1-c.1)-d.S) := by
    rw [he]
    change 0 < controlDeterminant lam d (c.1,w.1,c.2.2)
    linarith [hd.determinant_positive hc']
  have hscore : 0 ≤ w.2-A+Certificates.Control.theta (2*lam-c.2.1) (c.1+c.2.2-lam)
      (primitive lam d c.1) (quadratic lam (1-c.1)-d.S) A B*(w.1-c.2.1) := by
    change 0 ≤ w.2-A+featureTheta lam d (c,A,B)*(w.1-c.2.1)
    nlinarith only [hs]
  have hv := Certificates.Control.value_x_shift_nonincreasing (z-lam) (2*lam-c.2.1)
    (c.1+c.2.2-lam) (primitive lam d c.1) (quadratic lam (1-c.1)-d.S)
    (quadratic lam (z-c.1)-d.S-u) A B (w.1-c.2.1) (w.2-A) hD hD'
    (by linarith [(hd.control_coefficients_positive hc hz huLow huHigh).1]) hscore
  have ht := Certificates.Control.theta_x_shift_nondecreasing (2*lam-c.2.1)
    (c.1+c.2.2-lam) (primitive lam d c.1) (quadratic lam (1-c.1)-d.S)
    A B (w.1-c.2.1) (w.2-A) hD hD'
    (by linarith [hd.control_R_lower hc.1]) hscore
  rw [he,add_sub_cancel] at hv ht
  constructor
  · rw [featureH_eq_value hd z u w.2 B hc',featureH_eq_value hd z u A B hc]
    exact hv
  · exact ht

theorem Admissible.feature_y_replacement {lam z u A B : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {c : Control} (hc : c ∈ controlDomain)
    (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    {w : ℝ × ℝ} (hw : w.1 ∈ Icc xLo xHi) (hpw : c.1 ≤ w.1)
    (hs : B+featureTheta lam d (c,A,B)*c.2.2 ≤ w.2+featureTheta lam d (c,A,B)*w.1) :
    featureH hd z u ((c.1,c.2.1,w.1),A,w.2) ≤ featureH hd z u (c,A,B) ∧
    featureTheta lam d (c,A,B) ≤ featureTheta lam d ((c.1,c.2.1,w.1),A,w.2) := by
  have hc' : (c.1,c.2.1,w.1) ∈ controlDomain := ⟨hc.1,hc.2.1,⟨max_le hw.1 hpw,hw.2⟩⟩
  have he : (c.1+c.2.2-lam)+(w.1-c.2.2) = c.1+w.1-lam := by ring
  have hD : 0 < Certificates.Control.det (2*lam-c.2.1) (c.1+c.2.2-lam)
      (primitive lam d c.1) (quadratic lam (1-c.1)-d.S) := by
    change 0 < controlDeterminant lam d c
    linarith [hd.determinant_positive hc]
  have hD' : 0 < Certificates.Control.det (2*lam-c.2.1) ((c.1+c.2.2-lam)+(w.1-c.2.2))
      (primitive lam d c.1) (quadratic lam (1-c.1)-d.S) := by
    rw [he]
    change 0 < controlDeterminant lam d (c.1,c.2.1,w.1)
    linarith [hd.determinant_positive hc']
  have hscore : 0 ≤ w.2-B+Certificates.Control.theta (2*lam-c.2.1) (c.1+c.2.2-lam)
      (primitive lam d c.1) (quadratic lam (1-c.1)-d.S) A B*(w.1-c.2.2) := by
    change 0 ≤ w.2-B+featureTheta lam d (c,A,B)*(w.1-c.2.2)
    nlinarith only [hs]
  have hv := Certificates.Control.value_y_shift_nonincreasing (z-lam) (2*lam-c.2.1)
    (c.1+c.2.2-lam) (primitive lam d c.1) (quadratic lam (1-c.1)-d.S)
    (quadratic lam (z-c.1)-d.S-u) A B (w.1-c.2.2) (w.2-B) hD hD'
    (by linarith [(hd.control_coefficients_positive hc hz huLow huHigh).2]) hscore
  have ht := Certificates.Control.theta_y_shift_nondecreasing (2*lam-c.2.1)
    (c.1+c.2.2-lam) (primitive lam d c.1) (quadratic lam (1-c.1)-d.S)
    A B (w.1-c.2.2) (w.2-B) hD hD' (hd.control_P_bounds hc.1).1 hscore
  rw [he,add_sub_cancel] at hv ht
  constructor
  · rw [featureH_eq_value hd z u A w.2 hc',featureH_eq_value hd z u A B hc]
    exact hv
  · exact ht

end OptimalG.Variational
