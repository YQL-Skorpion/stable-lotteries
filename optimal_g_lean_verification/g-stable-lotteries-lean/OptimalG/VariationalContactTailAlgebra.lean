import OptimalG.PolynomialCompletion

/-! The terminal-contact equation simplifies the Hermite coefficients.
The quadratic tail coefficient is nonpositive analytically; it need not be
certified by interval subdivision. Here a=lambda-q and h=1-z. -/
namespace OptimalG.Variational

theorem contact_initial_tail_slope {a h sigma E : ℝ}
    (ha : a≠0) (hh : h≠0) (hcontact : h^2=2*a*sigma-2*E) :
    tailOne (1-h) ((1-h)*(h-sigma)) (-1+2*h-sigma+(1-h)*h/a)/h=
      -2+(3*h-1)/a+2*E*(3-h)/(a*h^2) := by
  have hs : sigma=(h^2+2*E)/(2*a) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) ha)).mpr
    nlinarith only [hcontact]
  rw [hs]
  unfold tailOne
  have he : 1-(1-h)=h := by ring
  rw [he]
  field_simp [ha,hh]
  ring

theorem contact_tailTwo_identity {a h sigma E : ℝ}
    (ha : a≠0) (hh : h≠0) (hcontact : h^2=2*a*sigma-2*E) :
    tailTwo (1-h) ((1-h)*(h-sigma)) (-1+2*h-sigma+(1-h)*h/a)*h*a=
      -3*h*a*sigma-6*(1-h)*E := by
  have hs : sigma=(h^2+2*E)/(2*a) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) ha)).mpr
    nlinarith only [hcontact]
  rw [hs]
  unfold tailTwo
  have he : 1-(1-h)=h := by ring
  rw [he]
  field_simp [ha,hh]
  ring

theorem contact_tailTwo_nonpos {a h sigma E : ℝ}
    (ha : 0<a) (hh : 0<h) (hh1 : h≤1) (hs : 0≤sigma) (hE : 0≤E)
    (hcontact : h^2=2*a*sigma-2*E) :
    tailTwo (1-h) ((1-h)*(h-sigma)) (-1+2*h-sigma+(1-h)*h/a)≤0 := by
  have hid := contact_tailTwo_identity ha.ne' hh.ne' hcontact
  have h1 := mul_nonneg (mul_nonneg hh.le ha.le) hs
  have h2 := mul_nonneg (sub_nonneg.mpr hh1) hE
  have hp : tailTwo (1-h) ((1-h)*(h-sigma)) (-1+2*h-sigma+(1-h)*h/a)*(h*a)≤0 := by
    nlinarith only [hid,h1,h2]
  exact nonpos_of_mul_nonpos_left hp (mul_pos hh ha)

end OptimalG.Variational
