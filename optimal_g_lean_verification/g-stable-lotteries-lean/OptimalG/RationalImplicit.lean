import OptimalG.WeightedElection
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

/-!
# Rational probability parameters in an implicit equation

This is the analytic correction step used in converting weighted elections to
uniform voters. An invertible lottery derivative lets one replace the voter
probabilities by exact rational probabilities and preserve the score equations,
while staying in any prescribed neighborhood. The regularity and invertibility
hypotheses are explicit; this module does not claim them for an election yet.
-/

namespace OptimalG
open Set Filter
open scoped Topology

/-- Rational finite voter probabilities preserve a regular implicit equation,
with the accompanying variable kept in any prescribed joint neighborhood. -/
theorem exists_rational_parameter_implicit
    {V : Type*} [Fintype V]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : (V → ℝ) × E → F) (f' : (V → ℝ) × E →L[ℝ] F)
    (w : V → ℝ) (y : E) (hw : ∀ v, 0 ≤ w v) (hsum : ∑ v, w v = 1)
    (hderiv : HasStrictFDerivAt f f' (w, y))
    (hinvertible : (f' ∘L ContinuousLinearMap.inr ℝ (V → ℝ) E).IsInvertible)
    (U : Set ((V → ℝ) × E)) (hU : U ∈ 𝓝 (w, y)) :
    ∃ copies : V → ℕ, 0 < ∑ v, copies v ∧ ∃ y' : E,
      (copyWeight copies, y') ∈ U ∧ f (copyWeight copies, y') = f (w, y) := by
  let correction := hderiv.implicitFunctionOfProdDomain hinvertible
  have htendsto : Tendsto correction (𝓝 w) (𝓝 y) :=
    hderiv.tendsto_implicitFunctionOfProdDomain hinvertible
  have hnear : ∀ᶠ w' in 𝓝 w, (w', correction w') ∈ U :=
    (tendsto_id.prodMk_nhds htendsto).eventually hU
  have heq : ∀ᶠ w' in 𝓝 w, f (w', correction w') = f (w, y) :=
    hderiv.eventually_apply_implicitFunctionOfProdDomain hinvertible
  obtain ⟨copies, hcopies, hmem, hequal⟩ := exists_copyWeight_mem_nhds w hw hsum
    {w' | (w', correction w') ∈ U ∧ f (w', correction w') = f (w, y)} (hnear.and heq)
  exact ⟨copies, hcopies, correction (copyWeight copies), hmem, hequal⟩

end OptimalG
