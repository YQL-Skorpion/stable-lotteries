import OptimalG.Certificates.Control
import OptimalG.VariationalDefs

/-! The exact early/late transported-control coefficients used in Appendix B.4.
These definitions reproduce the rational expressions in the supplied numerical
certificate code, and are algebraically identified with the actual controlH. -/
namespace OptimalG.Certificates.Transport

noncomputable def P (L S r : ℝ) : ℝ := quadratic L (1-r)-S
noncomputable def K (L M z r : ℝ) : ℝ := quadratic L (z-r)-M
noncomputable def h (L a : ℝ) : ℝ := 2*L-a
noncomputable def earlyK (L r a : ℝ) : ℝ := r+a-L
noncomputable def lateK (L r : ℝ) : ℝ := 2*r-L

noncomputable def earlyDenominator (L S r a R : ℝ) : ℝ := h L a*R-earlyK L r a*P L S r
noncomputable def lateDenominator (L S r a R : ℝ) : ℝ := h L a*R-lateK L r*P L S r

noncomputable def earlyNumerator0 (L r : ℝ) : ℝ := L+r
noncomputable def earlyNumerator1 (L M S z r R : ℝ) : ℝ :=
  (z-L)*(R+P L S r)+(L+r)*K L M z r
noncomputable def lateNumerator0 (L a : ℝ) : ℝ := h L a
noncomputable def lateNumerator1 (L r : ℝ) : ℝ := lateK L r
noncomputable def lateNumerator2 (L M S z r a : ℝ) : ℝ :=
  (z-L)*P L S r+h L a*K L M z r
noncomputable def lateNumerator3 (L M z r R : ℝ) : ℝ :=
  (z-L)*R+lateK L r*K L M z r

noncomputable def earlyAlpha (L S r a R A : ℝ) : ℝ :=
  earlyNumerator0 L r*A/earlyDenominator L S r a R
noncomputable def earlyBeta (L M S z r a R A : ℝ) : ℝ :=
  earlyNumerator1 L M S z r R*A/earlyDenominator L S r a R
noncomputable def lateAlpha (L S r a R A B : ℝ) : ℝ :=
  (lateNumerator0 L a*B+lateNumerator1 L r*A)/lateDenominator L S r a R
noncomputable def lateBeta (L M S z r a R A B : ℝ) : ℝ :=
  (lateNumerator2 L M S z r a*B+lateNumerator3 L M z r R*A)/lateDenominator L S r a R

/-- On the early branch both support ranks equal a. With Z=M-S-Y, the
negative control is exactly alpha*Z+beta. This identity needs no positivity
assumption and remains true under Lean's total division convention. -/
theorem early_transformed_control (L M S z r a R A Z : ℝ) :
    -Control.value (z-L) (h L a) (earlyK L r a) R (P L S r)
      (quadratic L (z-r)-S-(M-S-Z)) A A =
      earlyAlpha L S r a R A*Z+earlyBeta L M S z r a R A := by
  unfold Control.value Control.det Control.alphaNumerator earlyAlpha earlyBeta
    earlyNumerator0 earlyNumerator1 earlyDenominator K h earlyK
  ring

/-- On the late branch the second support rank equals r. A is the score at a,
B the score at r, matching the ordering of the manuscript's control. -/
theorem late_transformed_control (L M S z r a R A B Z : ℝ) :
    -Control.value (z-L) (h L a) (lateK L r) R (P L S r)
      (quadratic L (z-r)-S-(M-S-Z)) A B =
      lateAlpha L S r a R A B*Z+lateBeta L M S z r a R A B := by
  unfold Control.value Control.det Control.alphaNumerator lateAlpha lateBeta
    lateNumerator0 lateNumerator1 lateNumerator2 lateNumerator3 lateDenominator K
  ring

/-- The early branch is an actual control, with no minimizer assertion. -/
theorem early_controlH (L M z r a Z : ℝ) (d : Variational.LowRankData) :
    -Variational.controlH L d z (M-d.S-Z) (r,a,a) =
      earlyAlpha L d.S r a (Variational.primitive L d r) (d.phi a)*Z+
      earlyBeta L M d.S z r a (Variational.primitive L d r) (d.phi a) := by
  convert early_transformed_control L M d.S z r a (Variational.primitive L d r) (d.phi a) Z using 1
  simp only [Variational.controlH,Variational.controlDeterminant,Control.value,
    Control.det,Control.alphaNumerator,h,earlyK,P,Variational.quadratic,quadratic]

/-- The late branch is an actual control, with the rank constraint r≥a
handled separately when membership in the control domain is required. -/
theorem late_controlH (L M z r a Z : ℝ) (d : Variational.LowRankData) :
    -Variational.controlH L d z (M-d.S-Z) (r,a,r) =
      lateAlpha L d.S r a (Variational.primitive L d r) (d.phi a) (d.phi r)*Z+
      lateBeta L M d.S z r a (Variational.primitive L d r) (d.phi a) (d.phi r) := by
  convert late_transformed_control L M d.S z r a (Variational.primitive L d r) (d.phi a) (d.phi r) Z using 1 <;>
    simp only [Variational.controlH,Variational.controlDeterminant,Control.value,
      Control.det,Control.alphaNumerator,h,lateK,P,Variational.quadratic,quadratic,
      Prod.fst,Prod.snd] <;> ring

end OptimalG.Certificates.Transport
