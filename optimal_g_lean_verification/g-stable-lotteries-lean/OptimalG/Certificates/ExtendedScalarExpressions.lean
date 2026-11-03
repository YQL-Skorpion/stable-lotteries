import OptimalG.ExtendedCoefficients
import OptimalG.Certificates.SmallMassExpressions

/-! Polynomial numerators for the extended C.4 coefficients. The denominator
is positive on the actual middle primitive; coefficient certificates check
these displayed polynomials, then the algebraic bridge restores division. -/
namespace OptimalG.Certificates.ExtendedScalarExpressions
open Set Variational

noncomputable def denominator (lam S p t : ℝ) : ℝ :=
  (lam-t)*(Variational.quadratic lam p-S)+(lam-p)*(Variational.quadratic lam (1-p)-S)
noncomputable def etaNumerator (lam S p t : ℝ) : ℝ :=
  (2*lam-t)*(Variational.quadratic lam p-S)-(2*p-lam)*(Variational.quadratic lam (1-p)-S)
noncomputable def betaNumerator (lam p t : ℝ) : ℝ := lam^2-t*p
noncomputable def denominatorDerivative (lam S p t : ℝ) : ℝ :=
  (lam-t)*(lam-p)-(Variational.quadratic lam (1-p)-S)+(lam-p)*(1-p-lam)
noncomputable def etaNumeratorDerivative (lam S p t : ℝ) : ℝ :=
  (2*lam-t)*(lam-p)-2*(Variational.quadratic lam (1-p)-S)-(2*p-lam)*(1-p-lam)
noncomputable def etaDecrease (lam S p t : ℝ) : ℝ :=
  denominatorDerivative lam S p t*etaNumerator lam S p t-
    etaNumeratorDerivative lam S p t*denominator lam S p t
noncomputable def binaryGap (lam S p : ℝ) : ℝ :=
  lam*(Variational.quadratic lam p-S)-p*(Variational.quadratic lam (1-p)-S)
noncomputable def massSlack (lam S p t : ℝ) : ℝ :=
  denominator lam S p t+betaNumerator lam p t*p-etaNumerator lam S p t
noncomputable def firstSplit (lam S p t : ℝ) : ℝ :=
  betaNumerator lam p t*(SmallMassExpressions.initial lam S-lam+1-p)-denominator lam S p t
noncomputable def localSplit (lam S p t : ℝ) : ℝ :=
  betaNumerator lam p t*(SmallMassExpressions.initial lam S-lam+391/500-p)-denominator lam S p t

noncomputable def thetaSlack (lam S p t : ℝ) : ℝ :=
  (81/100)*etaNumerator lam S p t-denominator lam S p t
noncomputable def alphaSlack (lam S p t : ℝ) : ℝ :=
  3*etaNumerator lam S p t-betaNumerator lam p t

theorem denominator_eq (lam S p t : ℝ) : denominator lam S p t=
    extendedDenom lam p t (Variational.quadratic lam p-S) (Variational.quadratic lam (1-p)-S) := rfl

theorem eta_eq (lam S p t : ℝ) :
    extendedEta lam p t (Variational.quadratic lam p-S) (Variational.quadratic lam (1-p)-S)=
      etaNumerator lam S p t/denominator lam S p t := rfl

theorem beta_eq (lam S p t : ℝ) :
    extendedBeta lam p t (Variational.quadratic lam p-S) (Variational.quadratic lam (1-p)-S)=
      betaNumerator lam p t/denominator lam S p t := rfl

end OptimalG.Certificates.ExtendedScalarExpressions
