import OptimalG.StableFixedPoint
import OptimalG.ClippedElection
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Every finite election admits a stable lottery

Continuity at zero candidate mass follows directly from the averaged rank
integral. Thus the fixed-point construction applies on the entire closed
simplex, including its boundary.
-/

namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

/-- Actual activation, including at zero mass, is continuous in all masses. -/
theorem orderedActivation_continuous {m : ℕ} (g : ℝ → ℝ) (hg : Continuous g)
    (order : Equiv.Perm (Fin m)) (a : Fin m) :
    Continuous (fun D : Fin m → ℝ => orderedActivation g D order a) := by
  have harg : Continuous (fun q : (Fin m → ℝ) × ℝ =>
      rankPrefixLinear order a q.1 + q.2 * q.1 a) :=
    ((rankPrefixLinear order a).continuous.comp continuous_fst).add
      (continuous_snd.mul ((continuous_apply a).comp continuous_fst))
  have hint := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun (D : Fin m → ℝ) u => g (rankPrefixLinear order a D + u * D a))
    (hg.comp harg) 0 1
  simpa only [orderedActivation, rankActivation, rankPrefixLinear_apply,
    Equiv.apply_symm_apply] using hint

/-- Existence requires only continuity on the rank interval; no differentiability,
strict monotonicity, or positive-mass hypothesis is imposed. -/
theorem Election.exists_stable (E : Election) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 1)) :
    ∃ D : Lottery E.candidateCount, E.Stable g D := by
  let gc := clippedActivation g
  have hgc : Continuous gc := clippedActivation_continuous g hg
  let score := fun (D : E.Candidate → ℝ) a =>
    expectation E.voterWeight (fun v => orderedActivation gc D (E.order v) a)
  have hcont (a : E.Candidate) : Continuous (fun D => score D a) := by
    change Continuous (fun D => ∑ v, E.voterWeight v * orderedActivation gc D (E.order v) a)
    exact continuous_finsetSum _ (fun v _ => continuous_const.mul
      (orderedActivation_continuous gc hgc (E.order v) a))
  have hpartition (D : E.Candidate → ℝ) (hD : D ∈ stdSimplex ℝ E.Candidate) :
      expectation D (score D) = ∫ r in (0 : ℝ)..1, gc r := by
    dsimp only [score]
    rw [expectation_commute]
    simp_rw [ordered_integral_partition gc D _ hgc.continuousOn hD.1 hD.2]
    exact expectation_const E.voterWeight_total _
  obtain ⟨D, hD, hscore⟩ := exists_simplex_score_bound score (∫ r in (0 : ℝ)..1, gc r)
    (fun a => (hcont a).continuousOn) hpartition
  let lottery : Lottery E.candidateCount := ⟨D, hD.1, hD.2⟩
  refine ⟨lottery, (E.stable_clipped_iff g lottery).mp ?_⟩
  exact hscore

end OptimalG
