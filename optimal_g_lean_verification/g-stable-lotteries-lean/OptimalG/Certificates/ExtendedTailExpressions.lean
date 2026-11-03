import OptimalG.Certificates.ExtendedSelectedExpressions
import OptimalG.TailAnchorOrder

/-! Direct fixed-anchor scalar residuals for the full extended-mass tail.
The anchor height is the lower certified bound; only the two anchor-score
endpoints remain after the monotonicity theorem. -/
namespace OptimalG.Certificates.ExtendedTailExpressions
open ExtendedScalarExpressions ExtendedSelectedExpressions

noncomputable def base (lam S p t z Y H : ℝ) : ℝ :=
  denominator lam S p t*(z-lam)+betaNumerator lam p t*
    (p*(z-lam-p/2)+Variational.quadratic lam z-S-tailPrimitive (539/625) Y H z)+
    etaNumerator lam S p t*tailScore (539/625) Y H z

noncomputable def headCore (lam S p t z Y H q : ℝ) : ℝ :=
  base lam S p t z Y H+q*headLinear lam S p t z-
    betaNumerator lam p t*(1+SmallMassExpressions.slope lam S)*q^2/2

noncomputable def headCleared (lam S p t z Y H : ℝ) : ℝ :=
  2*betaNumerator lam p t*(1+SmallMassExpressions.slope lam S)*base lam S p t z Y H+
    (headLinear lam S p t z)^2

noncomputable def highCore (lam S p t z Y H q : ℝ) : ℝ :=
  base lam S p t z Y H+
    q*(denominator lam S p t-betaNumerator lam p t*(z-p))+betaNumerator lam p t*S

noncomputable def capCore (lam S p t z Y H q : ℝ) : ℝ :=
  headCore lam S p t z Y H q+betaNumerator lam p t*
    (Variational.cap lam S (z-p+q)-Variational.quadratic lam (z-p+q)+S)

noncomputable def capCoreCleared (lam S p t z Y H q : ℝ) : ℝ :=
  (1-(z-p+q))*headCore lam S p t z Y H q+betaNumerator lam p t*
    ((1-(z-p+q))*(lam^2-lam/2+lam*(z-p+q)/2-Variational.quadratic lam (z-p+q)+S)-lam*S)

theorem capCore_cleared_identity (lam S p t z Y H q : ℝ) (ha : z-p+q≠1) :
    capCoreCleared lam S p t z Y H q=(1-(z-p+q))*capCore lam S p t z Y H q := by
  have hn : 1-(z-p+q)≠0 := sub_ne_zero.mpr ha.symm
  unfold capCoreCleared capCore Variational.cap
  field_simp [hn]
  ring

theorem capCore_nonpos_of_cleared {lam S p t z Y H q : ℝ}
    (ha : z-p+q<1) (hh : capCoreCleared lam S p t z Y H q≤0) :
    capCore lam S p t z Y H q≤0 := by
  rw [capCore_cleared_identity lam S p t z Y H q ha.ne] at hh
  exact nonpos_of_mul_nonpos_right hh (sub_pos.mpr ha)

theorem core_identity {phi : ℝ→ℝ} {lam S p t q z Y H su eu : ℝ}
    (hphi : phi z=tailScore (539/625) Y H z)
    (hJ : curvePrimitive phi z=tailPrimitive (539/625) Y H z) :
    extendedHighCore lam S p t q z (primitiveDefect phi lam S z) su eu (phi z)=
      base lam S p t z Y H+
        q*(denominator lam S p t-betaNumerator lam p t*(z-p))+betaNumerator lam p t*(su+eu) := by
  unfold extendedHighCore primitiveDefect base
  rw [hphi,hJ]
  ring

theorem headCore_identity (lam S p t z Y H q : ℝ) :
    headCore lam S p t z Y H q=base lam S p t z Y H+
      q*(denominator lam S p t-betaNumerator lam p t*(z-p))+
      betaNumerator lam p t*(Variational.quadratic lam q-SmallMassExpressions.primitive lam S q) := by
  unfold headCore headLinear Variational.quadratic SmallMassExpressions.primitive
  ring

/-- The head maximum is bounded by the cleared full square when the
quadratic coefficient is positive. -/
theorem headCore_nonpos_of_cleared {lam S p t z Y H q : ℝ}
    (hJ : 0<betaNumerator lam p t) (hs : 0<1+SmallMassExpressions.slope lam S)
    (hc : headCleared lam S p t z Y H≤0) : headCore lam S p t z Y H q≤0 := by
  have hk : 0<2*betaNumerator lam p t*(1+SmallMassExpressions.slope lam S) := by positivity
  have hsq := sq_nonneg (headLinear lam S p t z-
    betaNumerator lam p t*(1+SmallMassExpressions.slope lam S)*q)
  have hid : (2*betaNumerator lam p t*(1+SmallMassExpressions.slope lam S))*
      headCore lam S p t z Y H q=
      headCleared lam S p t z Y H-
        (headLinear lam S p t z-betaNumerator lam p t*(1+SmallMassExpressions.slope lam S)*q)^2 := by
    unfold headCore headCleared
    ring
  have hh : (2*betaNumerator lam p t*(1+SmallMassExpressions.slope lam S))*
      headCore lam S p t z Y H q≤0 := by rw [hid]; linarith only [hc,hsq]
  exact nonpos_of_mul_nonpos_right hh hk

end OptimalG.Certificates.ExtendedTailExpressions
