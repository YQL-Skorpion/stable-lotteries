import OptimalG.Certificates.IntermediateTailExpressions

namespace OptimalG.Certificates.IntermediateTailExpressions
open Variational

/-- Clearing the sole cap denominator gives a polynomial target. -/
noncomputable def capCoreCleared (lam S p z Y H q : ℝ) : ℝ :=
  (1-(z-p+q))*headCore lam S p z Y H q+
    weight lam S p*((1-(z-p+q))*(lam^2-lam/2+lam*(z-p+q)/2-
      Variational.quadratic lam (z-p+q)+S)-lam*S)

theorem capCoreCleared_identity {lam S p z Y H q : ℝ} (hd : z-p+q<1) :
    capCoreCleared lam S p z Y H q=(1-(z-p+q))*capCore lam S p z Y H q := by
  have hn : 1-(z-p+q)≠0 := (sub_pos.mpr hd).ne'
  unfold capCoreCleared capCore Variational.cap
  field_simp [hn]
  ring

theorem capCore_nonpos_of_cleared {lam S p z Y H q : ℝ}
    (hd : z-p+q<1) (hc : capCoreCleared lam S p z Y H q≤0) :
    capCore lam S p z Y H q≤0 := by
  rw [capCoreCleared_identity hd] at hc
  exact nonpos_of_mul_nonpos_right hc (sub_pos.mpr hd)

end OptimalG.Certificates.IntermediateTailExpressions
