import OptimalG.VariationalContactTailAlgebra
import OptimalG.TailContact
import OptimalG.Certificates.TensorBernstein

/-! Polynomial numerators for the terminal-contact shape tests. The actual
contact equation makes each joining-slope residual affine in h=1-z. -/
namespace OptimalG.Certificates.TerminalShape
open OptimalG.Variational

noncomputable def denominator (q : ℝ) : ℝ := (1-q)^2
noncomputable def slackNumerator (lam S q : ℝ) : ℝ :=
  (lam/2-q)*denominator q+lam*S
noncomputable def deficitNumerator (lam S q : ℝ) : ℝ :=
  (S+lam^2-lam/2-lam*q/2+q^2/2)*denominator q-lam*S*(1-q)
noncomputable def contactNumerator (lam S q : ℝ) : ℝ :=
  2*(lam-q)*slackNumerator lam S q-2*deficitNumerator lam S q
noncomputable def joinNumerator (lam S q h : ℝ) : ℝ :=
  contactNumerator lam S q*((lam-q)*(1.22*denominator q-
    4.53*(slackNumerator lam S q+(lam+0.36)*denominator q))+denominator q)+
  (4.53*(lam-q)+1.53)*contactNumerator lam S q*h*denominator q-
  4.53*(contactNumerator lam S q)^2-6*deficitNumerator lam S q*denominator q+
  2*deficitNumerator lam S q*h*denominator q
noncomputable def tailNumerator (lam S q h : ℝ) : ℝ :=
  ((lam-q+1)*contactNumerator lam S q-6*deficitNumerator lam S q+
    h*(2*deficitNumerator lam S q-3*contactNumerator lam S q))*denominator q

theorem slackNumerator_eq (lam S q : ℝ) (hq : q≠1) :
    slackNumerator lam S q=capSlack lam S q*denominator q := by
  have hd : (1-q)^2≠0 := pow_ne_zero _ (sub_ne_zero.mpr hq.symm)
  unfold slackNumerator denominator capSlack capScore
  field_simp [hd]
  ring

theorem deficitNumerator_eq (lam S q : ℝ) (hq : q≠1) :
    deficitNumerator lam S q=capDeficit lam S q*denominator q := by
  unfold deficitNumerator denominator capDeficit Variational.quadratic Variational.cap
  field_simp [sub_ne_zero.mpr hq.symm]
  ring

theorem contactNumerator_eq (lam S q : ℝ) (hq : q≠1) :
    contactNumerator lam S q=
      (2*(lam-q)*capSlack lam S q-2*capDeficit lam S q)*denominator q := by
  rw [contactNumerator,slackNumerator_eq lam S q hq,deficitNumerator_eq lam S q hq]
  ring

theorem joinNumerator_affine (lam S q h h0 h1 : ℝ) :
    (h1-h0)*joinNumerator lam S q h=
      (h1-h)*joinNumerator lam S q h0+(h-h0)*joinNumerator lam S q h1 := by
  unfold joinNumerator
  ring

theorem tailNumerator_affine (lam S q h h0 h1 : ℝ) :
    (h1-h0)*tailNumerator lam S q h=
      (h1-h)*tailNumerator lam S q h0+(h-h0)*tailNumerator lam S q h1 := by
  unfold tailNumerator
  ring

theorem joinNumerator_contact_identity {lam S q h : ℝ}
    (ha : lam-q≠0) (hh : h≠0) (hq : q≠1)
    (hc : h^2=2*(lam-q)*capSlack lam S q-2*capDeficit lam S q) :
    joinNumerator lam S q h =
      (-0.78+4.53*((-1+2*h-capSlack lam S q+(1-h)*h/(lam-q))-lam+1-h-0.36)-
        tailOne (1-h) ((1-h)*(h-capSlack lam S q))
          (-1+2*h-capSlack lam S q+(1-h)*h/(lam-q))/h)*
        (lam-q)*h^2*(denominator q)^2 := by
  rw [contact_initial_tail_slope ha hh hc]
  unfold joinNumerator
  rw [contactNumerator_eq lam S q hq,slackNumerator_eq lam S q hq,
    deficitNumerator_eq lam S q hq,←hc]
  field_simp [ha,hh]
  ring

theorem tailNumerator_contact_identity {lam S q h : ℝ}
    (ha : lam-q≠0) (hh : h≠0) (hq : q≠1)
    (hc : h^2=2*(lam-q)*capSlack lam S q-2*capDeficit lam S q) :
    tailNumerator lam S q h =
      (-1-tailOne (1-h) ((1-h)*(h-capSlack lam S q))
        (-1+2*h-capSlack lam S q+(1-h)*h/(lam-q))/h)*
        (lam-q)*h^2*(denominator q)^2 := by
  rw [contact_initial_tail_slope ha hh hc]
  unfold tailNumerator
  rw [contactNumerator_eq lam S q hq,deficitNumerator_eq lam S q hq,←hc]
  field_simp [ha,hh]
  ring

end OptimalG.Certificates.TerminalShape
