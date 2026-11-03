import OptimalG.ScoreDerivative
import OptimalG.Election

/-! # Continuous clipping preserves the actual election problem exactly -/

namespace OptimalG
open Set MeasureTheory

theorem clippedActivation_mean (g : ℝ → ℝ) :
    (∫ r in (0 : ℝ)..1, clippedActivation g r) = ∫ r in (0 : ℝ)..1, g r := by
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hr
  exact clippedActivation_eq g r hr

theorem Election.activation_clipped (E : Election) (g : ℝ → ℝ)
    (D : Lottery E.candidateCount) (v : E.Voter) (a : E.Candidate) :
    E.activation (clippedActivation g) D v a = E.activation g D v a :=
  orderedActivation_clipped g D.weight D.nonneg D.total (E.order v) a

theorem Election.stable_clipped_iff (E : Election) (g : ℝ → ℝ)
    (D : Lottery E.candidateCount) : E.Stable (clippedActivation g) D ↔ E.Stable g D := by
  simp only [Election.Stable, Election.activation_clipped, clippedActivation_mean]

theorem witnessAbove_clipped_iff (g : ℝ → ℝ) (K : ℝ) :
    WitnessAbove (clippedActivation g) K ↔ WitnessAbove g K := by
  simp only [WitnessAbove, Election.stable_clipped_iff]

theorem universalBound_clipped_iff (g : ℝ → ℝ) (K : ℝ) :
    UniversalBound (clippedActivation g) K ↔ UniversalBound g K := by
  simp only [UniversalBound, Election.stable_clipped_iff]

end OptimalG
