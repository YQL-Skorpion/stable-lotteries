import OptimalG.TailReanchor

/-! Cancellation-free backward coefficients of a rational terminal contact.
These identities use the actual contact equation, not an independent box for
the contact value and slope. -/
namespace OptimalG

theorem contact_backward_slope {a h sigma E : ℝ}
    (ha : a≠0) (hh : h≠0) (hc : h^2=2*a*sigma-2*E) :
    tailBackwardSlope (1-h) ((1-h)*(h-sigma))
      (-1+2*h-sigma+(1-h)*h/a)=2+1/a+(6-4*h)*E/(a*h^2) := by
  have hs : sigma=(h^2+2*E)/(2*a) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) ha)).mpr
    nlinarith only [hc]
  rw [hs]
  unfold tailBackwardSlope tailOne tailTwo
  have he : 1-(1-h)=h := by ring
  rw [he]
  field_simp [ha,hh]
  ring

theorem contact_backward_curvature {a h sigma E : ℝ}
    (ha : a≠0) (hh : h≠0) (hc : h^2=2*a*sigma-2*E) :
    tailBackwardCurvature (1-h) ((1-h)*(h-sigma))
      (-1+2*h-sigma+(1-h)*h/a)=3/(2*a)+3*(2-h)*E/(a*h^3) := by
  have hs : sigma=(h^2+2*E)/(2*a) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) ha)).mpr
    nlinarith only [hc]
  rw [hs]
  unfold tailBackwardCurvature tailTwo
  have he : 1-(1-h)=h := by ring
  rw [he]
  field_simp [ha,hh]
  ring

theorem contact_anchor_primitive {a h sigma E r : ℝ}
    (ha : a≠0) (hh : h≠0) (hc : h^2=2*a*sigma-2*E) :
    tailPrimitive (1-h) ((1-h)*(h-sigma))
      (-1+2*h-sigma+(1-h)*h/a) r=
      (1-r)-(2+1/a+(6-4*h)*E/(a*h^2))/2*(1-r)^2+
        (3/(2*a)+3*(2-h)*E/(a*h^3))/3*(1-r)^3 := by
  rw [tailPrimitive_backward _ _ _ _ (by intro he; apply hh; linarith only [he]),
    contact_backward_slope ha hh hc,contact_backward_curvature ha hh hc]

theorem contact_anchor_score {a h sigma E r : ℝ}
    (ha : a≠0) (hh : h≠0) (hc : h^2=2*a*sigma-2*E) :
    tailScore (1-h) ((1-h)*(h-sigma))
      (-1+2*h-sigma+(1-h)*h/a) r=
      -1+(2+1/a+(6-4*h)*E/(a*h^2))*(1-r)-
        (3/(2*a)+3*(2-h)*E/(a*h^3))*(1-r)^2 := by
  rw [tailScore_backward _ _ _ _ (by intro he; apply hh; linarith only [he]),
    contact_backward_slope ha hh hc,contact_backward_curvature ha hh hc]

end OptimalG
