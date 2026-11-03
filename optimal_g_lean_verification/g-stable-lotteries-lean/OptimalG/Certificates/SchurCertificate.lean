import OptimalG.Certificates.ExpressionAlgebra
import OptimalG.Certificates.Expression

/-! Sound three-variable Hessian lower bounds from the two-by-two Schur test
used by the reference transport certificates. -/
namespace OptimalG.Certificates

theorem schur_quadratic_lower {A B C D E F m mu : ℝ}
    (h1 : 0<D+m) (h2 : 0<F+m-E^2/(D+m))
    (hs : mu≤A-B^2/(D+m)-(C-E*B/(D+m))^2/(F+m-E^2/(D+m)))
    (s r a : ℝ) :
    mu*s^2-m*(r^2+a^2)≤A*s^2+2*B*s*r+2*C*s*a+D*r^2+2*E*r*a+F*a^2 := by
  generalize hd1 : D+m=d1 at h1 h2 hs
  generalize hd2 : F+m-E^2/d1=d2 at h2 hs
  have h1' : d1≠0 := ne_of_gt h1
  have h2' : d2≠0 := ne_of_gt h2
  have he : A*s^2+2*B*s*r+2*C*s*a+D*r^2+2*E*r*a+F*a^2-
      (mu*s^2-m*(r^2+a^2)) =
      d1*(r+E/d1*a+B/d1*s)^2+d2*(a+(C-E*B/d1)/d2*s)^2+
        (A-B^2/d1-(C-E*B/d1)^2/d2-mu)*s^2 := by
    have hD : D=d1-m := by linarith only [hd1]
    have hF : F=d2+E^2/d1-m := by linarith only [hd2]
    rw [hD,hF]
    field_simp [h1',h2']
    ring
  have hlast : 0≤A-B^2/d1-(C-E*B/d1)^2/d2-mu := sub_nonneg.mpr hs
  have hp : 0≤d1*(r+E/d1*a+B/d1*s)^2+d2*(a+(C-E*B/d1)/d2*s)^2+
      (A-B^2/d1-(C-E*B/d1)^2/d2-mu)*s^2 := by
    have hp1 : 0<d1 := h1
    have hp2 : 0<d2 := h2
    positivity
  rw [←he] at hp
  exact sub_nonneg.mp hp

namespace SchurCertificate

def d1 (m : ℚ) : RatExpr 6 := .var 3+.const m
def d2 (m : ℚ) : RatExpr 6 := .var 5+.const m-(.var 4*.var 4)/d1 m
def schur (m : ℚ) : RatExpr 6 :=
  .var 0-(.var 1*.var 1)/d1 m-
    ((.var 2-(.var 4*.var 1)/d1 m)*(.var 2-(.var 4*.var 1)/d1 m))/d2 m

def check (m mu : ℚ) (box : Fin 6 → RatInterval) : Bool :=
  (d1 m).lowerCheck box 0 && ((d2 m).lowerCheck box 0 && (schur m).lowerCheck box mu)

theorem check_sound {m mu : ℚ} {box : Fin 6 → RatInterval} {x : Fin 6 → ℝ}
    (hx : ∀ i,(box i).Contains (x i)) (hc : check m mu box=true) (s r a : ℝ) :
    (mu:ℝ)*s^2-(m:ℝ)*(r^2+a^2)≤
      x 0*s^2+2*x 1*s*r+2*x 2*s*a+x 3*r^2+2*x 4*r*a+x 5*a^2 := by
  have h := Bool.and_eq_true_iff.mp hc
  have h1 := RatExpr.lowerCheck_sound (d1 m) box 0 h.1 x hx
  have h2 := RatExpr.lowerCheck_sound (d2 m) box 0 (Bool.and_eq_true_iff.mp h.2).1 x hx
  have hs := RatExpr.lowerCheck_sound (schur m) box mu (Bool.and_eq_true_iff.mp h.2).2 x hx
  simp only [d1,d2,schur,RatExpr.eval,RatExpr.eval_addNotation,RatExpr.eval_mulNotation,RatExpr.eval_negNotation,RatExpr.eval_subNotation,RatExpr.eval_divNotation,RatExpr.eval_natNotation,Rat.cast_zero] at h1 h2 hs
  apply schur_quadratic_lower h1
  · simpa only [pow_two,div_eq_mul_inv] using h2
  · simpa only [pow_two,div_eq_mul_inv] using hs.le

end SchurCertificate
end OptimalG.Certificates
