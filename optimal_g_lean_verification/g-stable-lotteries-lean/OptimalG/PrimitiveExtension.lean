import OptimalG.NecessaryPrimitiveBounds
import Mathlib.Analysis.Calculus.MeanValue

/-! A globally Lipschitz extension of an actual continuous-score primitive.
Only the score is clipped; primitive values on the rank interval are unchanged. -/
namespace OptimalG
open Set MeasureTheory
open scoped NNReal

noncomputable def extendedPrimitive (phi : ℝ → ℝ) : ℝ → ℝ :=
  activationPrimitive (clippedActivation phi)

theorem extendedPrimitive_eq (phi : ℝ → ℝ) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    extendedPrimitive phi r = activationPrimitive phi r := activationPrimitive_clipped phi hr

theorem clippedActivation_bounded {phi : ℝ → ℝ} (hphi : ContinuousOn phi (Icc 0 1)) :
    ∃ K : ℝ≥0, ∀ r, ‖clippedActivation phi r‖ ≤ K := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hphi
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  intro r
  exact (hC (max 0 (min 1 r))
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩).trans (le_max_left _ _)

theorem extendedPrimitive_hasDerivAt {phi : ℝ → ℝ}
    (hphi : ContinuousOn phi (Icc 0 1)) (r : ℝ) :
    HasDerivAt (extendedPrimitive phi) (clippedActivation phi r) r := by
  have hc := clippedActivation_continuous phi hphi
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem extendedPrimitive_lipschitz {phi : ℝ → ℝ}
    (hphi : ContinuousOn phi (Icc 0 1)) :
    ∃ K : ℝ≥0, LipschitzWith K (extendedPrimitive phi) := by
  obtain ⟨K,hK⟩ := clippedActivation_bounded hphi
  refine ⟨K,lipschitzWith_of_nnnorm_deriv_le
    (fun r => (extendedPrimitive_hasDerivAt hphi r).differentiableAt) ?_⟩
  intro r
  rw [(extendedPrimitive_hasDerivAt hphi r).deriv]
  exact_mod_cast hK r

end OptimalG
