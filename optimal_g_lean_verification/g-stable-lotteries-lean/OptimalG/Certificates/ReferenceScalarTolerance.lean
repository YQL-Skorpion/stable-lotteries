import OptimalG.Certificates.ReferenceScalarCertificate

/-! Adjustable certified flow residual, preserving the original scalar certificate API. -/
namespace OptimalG.Certificates.Transport.ReferenceScalarCertificate
open Set

def checkWithTolerance (s : ℕ) (residual : ℤ) (c : ReferenceScalarCertificate) : Bool :=
  c.cell.flow.residualExpr.midpointTaylorCleanCheck s residual &&
  (c.cell.residualExpr c.polynomial).midpointSubdividedCheck s ((s/400000:ℕ):ℤ) c.depth &&
  c.cell.flow.alphaExpr.integerAbsCheck s (3*(s:ℤ)) &&
  c.cell.flow.betaExpr.integerAbsCheck s (1000*(s:ℤ)) &&
  c.cell.alphaSExpr.integerAbsCheck s (1000*(s:ℤ)) &&
  c.cell.betaSExpr.integerAbsCheck s (100000*(s:ℤ))

theorem checked_bounds_with_tolerance {s : ℕ} {residual : ℤ} (hs : 0<s) (c : ReferenceScalarCertificate)
    (hc : c.checkWithTolerance s residual=true) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    |c.cell.flow.valuePolynomial.derivative.eval t/(c.cell.flow.length:ℝ)-
      c.cell.flow.actualAlpha t*c.cell.flow.valuePolynomial.eval t-
      c.cell.flow.actualBeta t|≤(residual:ℝ)/(s:ℝ) ∧
    |c.polynomial.derivative.eval t/(c.cell.flow.length:ℝ)-
      c.cell.flow.actualAlpha t*c.polynomial.eval t-
      c.cell.actualAlphaS t*c.cell.flow.valuePolynomial.eval t-
      c.cell.actualBetaS t|≤((s/400000:ℕ):ℝ)/(s:ℝ) ∧
    |c.cell.flow.actualAlpha t|≤3 ∧ |c.cell.flow.actualBeta t|≤1000 ∧
    |c.cell.actualAlphaS t|≤1000 ∧ |c.cell.actualBetaS t|≤100000 := by
  have hh := hc
  simp only [checkWithTolerance,Bool.and_eq_true] at hh
  rcases hh with ⟨⟨⟨⟨⟨hX,hV⟩,ha⟩,hb⟩,has⟩,hbs⟩
  have hX' := RatExpr.midpointTaylorCleanCheck_sound hs _ _ hX ht
  have hV' := RatExpr.midpointSubdividedCheck_sound hs _ _ _ hV ht
  rw [c.cell.flow.residualExpr_eval] at hX'
  rw [c.cell.residualExpr_eval] at hV'
  have ha' := RatExpr.integerAbsCheck_sound hs _ _ ha ht
  have hb' := RatExpr.integerAbsCheck_sound hs _ _ hb ht
  have has' := RatExpr.integerAbsCheck_sound hs _ _ has ht
  have hbs' := RatExpr.integerAbsCheck_sound hs _ _ hbs ht
  have hs' : (s:ℝ)≠0 := ne_of_gt (by exact_mod_cast hs)
  simp only [c.cell.flow.alphaExpr_eval,c.cell.flow.betaExpr_eval,
    c.cell.alphaSExpr_eval,c.cell.betaSExpr_eval] at ha' hb' has' hbs'
  norm_num [Int.cast_mul,Int.cast_natCast,hs',mul_div_cancel_right₀] at ha' hb' has' hbs'
  exact ⟨hX',hV',ha',hb',has',hbs'⟩

end OptimalG.Certificates.Transport.ReferenceScalarCertificate
