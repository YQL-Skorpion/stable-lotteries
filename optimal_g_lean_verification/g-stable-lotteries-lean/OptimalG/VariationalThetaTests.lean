import OptimalG.VariationalSupportingFeatures

/-! Sharpening the supporting slope by testing two known low ranks, as in
B.3 Step 4. The inequalities are consequences of actual active supports. -/
namespace OptimalG.Variational
open Set

 theorem supporting_theta_test_bound {lam p x y R P A B theta t s f g : ℝ}
    (hR : 0 ≤ R) (hP : 0 ≤ P)
    (hbalance : theta*((2*lam-x)*R-(p+y-lam)*P)=R*A+P*B)
    (hx : f+theta*t ≤ A+theta*x) (hy : g+theta*s ≤ B+theta*y) :
    R*f+P*g ≤ theta*((2*lam-t)*R+(lam-p-s)*P) := by
  have hhx := mul_le_mul_of_nonneg_left hx hR
  have hhy := mul_le_mul_of_nonneg_left hy hP
  nlinarith only [hhx,hhy,hbalance]

 theorem active_feature_theta_test_bound {lam z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hactive : featureH hd z u v=vectorField lam d z u)
    {w1 w2 : ℝ × ℝ} (hw1 : w1 ∈ rankScoreSupport d.phi) (hw2 : w2 ∈ rankScoreSupport d.phi)
    (hp : v.1.1 ≤ w2.1) :
    primitive lam d v.1.1*w1.2+(quadratic lam (1-v.1.1)-d.S)*w2.2 ≤
      featureTheta lam d v*((2*lam-w1.1)*primitive lam d v.1.1+
        (lam-v.1.1-w2.1)*(quadratic lam (1-v.1.1)-d.S)) := by
  have hc := (hd.controlFeatureSupport_subset hv).1
  have hR : 0 ≤ primitive lam d v.1.1 := by linarith [hd.control_R_lower hc.1]
  have hP : 0 ≤ quadratic lam (1-v.1.1)-d.S := (hd.control_P_bounds hc.1).1
  have hD : (2*lam-v.1.2.1)*primitive lam d v.1.1-
      (v.1.1+v.1.2.2-lam)*(quadratic lam (1-v.1.1)-d.S) ≠ 0 := by
    change controlDeterminant lam d v.1 ≠ 0
    exact ne_of_gt (by linarith [hd.determinant_positive hc])
  have hbalance : featureTheta lam d v*((2*lam-v.1.2.1)*primitive lam d v.1.1-
      (v.1.1+v.1.2.2-lam)*(quadratic lam (1-v.1.1)-d.S)) =
      primitive lam d v.1.1*v.2.1+(quadratic lam (1-v.1.1)-d.S)*v.2.2 := by
    exact div_mul_cancel₀ _ hD
  exact supporting_theta_test_bound hR hP hbalance
    (active_feature_supports_x hd hz huLow huHigh hv hactive hw1)
    (active_feature_supports_y hd hz huLow huHigh hv hactive hw2 hp)

 theorem supporting_theta_ratio_lower {lam p t s R P f g theta : ℝ}
    (hP : 0 < P)
    (hden : 0 < (2*lam-t)*(R/P)+lam-p-s)
    (hbound : R*f+P*g ≤ theta*((2*lam-t)*R+(lam-p-s)*P)) :
    (f*(R/P)+g)/((2*lam-t)*(R/P)+lam-p-s) ≤ theta := by
  apply (div_le_iff₀ hden).mpr
  apply (mul_le_mul_iff_left₀ hP).mp
  have hR : (R/P)*P=R := div_mul_cancel₀ _ hP.ne'
  have hf := congrArg (fun q : ℝ => f*q) hR
  have htheta := congrArg (fun q : ℝ => theta*(2*lam-t)*q) hR
  nlinarith only [hbound,hf,htheta]

end OptimalG.Variational
