import OptimalG.Certificates.ExtendedLocalExpressions

/-! Scalar residuals for the three analytic selected-high split regions.
Every quantity is an explicit rational expression in the compact parameters. -/
namespace OptimalG.Certificates.ExtendedSelectedExpressions
open Variational ExtendedScalarExpressions ExtendedLocalExpressions

noncomputable def headLinear (lam S p t z : ℝ) : ℝ :=
  denominator lam S p t+betaNumerator lam p t*(lam-z+p-SmallMassExpressions.initial lam S)

noncomputable def headCore (lam S p t z e q : ℝ) : ℝ :=
  (p-9/25)*localCore lam S p t z e+etaNumerator lam S (9/25) t*
    (q*headLinear lam S p t z-
      betaNumerator lam p t*(1+SmallMassExpressions.slope lam S)*q^2/2)

noncomputable def headGain (lam S p t z e : ℝ) : ℝ :=
  (p-9/25)*localCore lam S p t z e+etaNumerator lam S (9/25) t*
    (max (headLinear lam S p t z) 0)^2/
      (2*betaNumerator lam p t*(1+SmallMassExpressions.slope lam S))

noncomputable def headGainCleared (lam S p t z e : ℝ) : ℝ :=
  2*betaNumerator lam p t*(1+SmallMassExpressions.slope lam S)*
    (p-9/25)*localCore lam S p t z e+
    etaNumerator lam S (9/25) t*(headLinear lam S p t z)^2

noncomputable def highRankCore (lam S p t z e q : ℝ) : ℝ :=
  (p-9/25)*localCore lam S p t z e+etaNumerator lam S (9/25) t*
    (q*(denominator lam S p t-betaNumerator lam p t*(z-p))+betaNumerator lam p t*S)

noncomputable def capCore (lam S p t z e q : ℝ) : ℝ :=
  headCore lam S p t z e q+etaNumerator lam S (9/25) t*betaNumerator lam p t*
    (Variational.cap lam S (z-p+q)-Variational.quadratic lam (z-p+q)+S)

/-- Clearing the sole variable Variational.cap denominator gives an explicit polynomial. -/
noncomputable def capCoreCleared (lam S p t z e q : ℝ) : ℝ :=
  (1-(z-p+q))*headCore lam S p t z e q+
    etaNumerator lam S (9/25) t*betaNumerator lam p t*
      ((1-(z-p+q))*(lam^2-lam/2+lam*(z-p+q)/2-
        Variational.quadratic lam (z-p+q)+S)-lam*S)

theorem capCore_cleared_identity (lam S p t z e q : ℝ) (ha : z-p+q≠1) :
    capCoreCleared lam S p t z e q=(1-(z-p+q))*capCore lam S p t z e q := by
  have hn : 1-(z-p+q)≠0 := sub_ne_zero.mpr ha.symm
  unfold capCoreCleared capCore Variational.cap
  field_simp [hn]
  ring

theorem capCore_nonpos_of_cleared {lam S p t z e q : ℝ}
    (ha : z-p+q<1) (hh : capCoreCleared lam S p t z e q≤0) :
    capCore lam S p t z e q≤0 := by
  rw [capCore_cleared_identity lam S p t z e q ha.ne] at hh
  exact nonpos_of_mul_nonpos_right hh (sub_pos.mpr ha)

theorem headCore_identity (lam S p t z e q : ℝ) :
    headCore lam S p t z e q=
      extendedCompareCore lam S (9/25) p t q z e
        (Variational.quadratic lam q-SmallMassExpressions.primitive lam S q) 0 := by
  unfold headCore headLinear localCore extendedCompareCore SmallMassExpressions.primitive Variational.quadratic
  ring

theorem highRankCore_identity (lam S p t z e q : ℝ) :
    highRankCore lam S p t z e q=extendedCompareCore lam S (9/25) p t q z e S 0 := by
  unfold highRankCore localCore extendedCompareCore
  ring

theorem capCore_identity (lam S p t z e q : ℝ) :
    capCore lam S p t z e q=
      extendedCompareCore lam S (9/25) p t q z e
        (Variational.quadratic lam q-SmallMassExpressions.primitive lam S q)
        (Variational.cap lam S (z-p+q)-Variational.quadratic lam (z-p+q)+S) := by
  unfold capCore
  rw [headCore_identity]
  unfold extendedCompareCore
  ring

end OptimalG.Certificates.ExtendedSelectedExpressions
