import OptimalG.Certificates.Control
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Rational control values are uniformly Lipschitz on every compact argument
set with nonzero denominators. No differentiability of the low score is used. -/
namespace OptimalG.Certificates.Control
open Set Filter
open scoped Topology NNReal

abbrev Arguments := Fin 8 → ℝ
noncomputable def argumentsValue (v : Arguments) : ℝ :=
  value (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
noncomputable def argumentsDet (v : Arguments) : ℝ := det (v 1) (v 2) (v 3) (v 4)

theorem argumentsValue_contDiffAt {v : Arguments} (hv : argumentsDet v ≠ 0) :
    ContDiffAt ℝ 1 argumentsValue v := by
  unfold argumentsValue value alphaNumerator
  apply ContDiffAt.div
  · fun_prop
  · unfold det
    fun_prop
  · exact hv

theorem argumentsValue_lipschitz_compact {K : Set Arguments} (hK : IsCompact K)
    (hD : ∀ v ∈ K, argumentsDet v ≠ 0) : ∃ L : ℝ≥0, LipschitzOnWith L argumentsValue K := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro v hv
  obtain ⟨L,U,hU,hL⟩ := (argumentsValue_contDiffAt (hD v hv)).exists_lipschitzOnWith
  exact ⟨L,U,mem_nhdsWithin_of_mem_nhds hU,hL⟩

end OptimalG.Certificates.Control
