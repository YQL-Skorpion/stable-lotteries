import OptimalG.ExtendedMassTest
import OptimalG.Certificates.ExtendedCoefficientChecks

/-! All coefficient and low-support hypotheses for the final C.4 range
follow from checked exact polynomial signs and the existing base support.
Only the separate high mixed-test verification remains an input here. -/
namespace OptimalG
open Set Variational Certificates.ExtendedScalarExpressions
open Certificates.ExtendedCoefficientChecks

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem extended_mass_test_with_checked_coefficients {S p t beta0 eta0 : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (9/25:ℝ) lam) (ht : t∈Icc (1529/5000:ℝ) (9/25))
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial lam S)
    (hline : ∀ r∈Icc (9/25:ℝ) (391/500),phi r=lam-r)
    (hprimitive : ∀ r∈Icc (9/25:ℝ) (31/40),curvePrimitive phi r=quadratic lam r-S)
    (hfall : ∀ a b,0≤a→a≤b→b≤391/500→a-b≤phi b-phi a)
    (hfirst : beta0*(quadratic lam (1-9/25)-S)+eta0*(lam-t)=2*lam-t)
    (hsecond : beta0*(quadratic lam (9/25)-S)-eta0*(lam-9/25)=2*(9/25)-lam)
    (hsupport : ∀ x∈Icc (0:ℝ) lam,x+eta0*phi x≤eta0*lam-(eta0-1)*t)
    (hhigh : ∀ z∈Icc (391/500:ℝ) 1,∀ q,0≤q→q≤p→
      z+q-lam+extendedBeta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*
        packingK phi p q z+
        extendedEta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*phi z≤0) :
    ThreeFunctionTest phi lam p
      (extendedBeta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p)))
      (extendedEta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))) := by
  have hR := hprimitive p ⟨hp.1,by linarith only [hp.2,hL.2]⟩
  have hP := hprimitive (1-p) ⟨by linarith only [hp.2,hL.2],by linarith only [hp.1]⟩
  have hbin : p*curvePrimitive phi (1-p)≤lam*curvePrimitive phi p := by
    rw [hR,hP]
    have hh := (binaryGap_pos hL hS hp).le
    unfold binaryGap at hh
    linarith only [hh]
  have he := eta_le_of_base_system hL hS hp ht hfirst hsecond
  have hb := coefficient_bounds hL hS hp ht
  rw [←hR,←hP] at he hb
  rw [←hinitial] at hb
  exact h.extended_mass_test
    ⟨by linarith only [hL.1],by linarith only [hL.2]⟩ hp
    ⟨by linarith only [ht.1],by linarith only [ht.2,hL.1]⟩
    hline hfall hbin he hb.1 hsupport hb.2 hhigh

end VerifierCurve
end OptimalG
