import OptimalG.Election
import OptimalG.BiasedMetric

/-! Strict universal-bound failures can always be witnessed with genuine metrics
and positive reference cost, including when the original reference cost is zero. -/
namespace OptimalG
open scoped BigOperators

namespace Election

theorem candidateCost_separated (E : Election) (d : E.Metric) (eps : ℝ) (heps : 0 < eps)
    (a : E.Candidate) :
    E.candidateCost (separatedMetricSpace d eps heps).toPseudoMetricSpace a =
      E.candidateCost d a + eps := by
  unfold candidateCost
  have hd (v : E.Voter) :
      @dist E.Point (separatedMetricSpace d eps heps).toPseudoMetricSpace.toDist
        (Sum.inl v) (Sum.inr a) = @dist E.Point d.toDist (Sum.inl v) (Sum.inr a) + eps :=
    separated_dist_of_ne d eps heps _ _ (by simp)
  simp_rw [hd]
  rw [expectation_add, expectation_const E.voterWeight_total]

theorem lotteryCost_separated (E : Election) (d : E.Metric) (eps : ℝ) (heps : 0 < eps)
    (D : Lottery E.candidateCount) :
    E.lotteryCost (separatedMetricSpace d eps heps).toPseudoMetricSpace D =
      E.lotteryCost d D + eps := by
  change expectation D.weight (fun a => E.candidateCost (separatedMetricSpace d eps heps).toPseudoMetricSpace a) =
    expectation D.weight (fun a => E.candidateCost d a) + eps
  simp_rw [E.candidateCost_separated d eps heps]
  rw [expectation_add, expectation_const D.total]

theorem consistent_separated (E : Election) (d : E.Metric) (hd : E.Consistent d)
    (eps : ℝ) (heps : 0 < eps) :
    E.Consistent (separatedMetricSpace d eps heps).toPseudoMetricSpace := by
  intro v b c hcb
  change @dist E.Point (separatedMetricSpace d eps heps).toPseudoMetricSpace.toDist
      (Sum.inl v) (Sum.inr b) ≤
    @dist E.Point (separatedMetricSpace d eps heps).toPseudoMetricSpace.toDist
      (Sum.inl v) (Sum.inr c)
  rw [separated_dist_of_ne d eps heps _ _ (by simp),
    separated_dist_of_ne d eps heps _ _ (by simp)]
  simpa only [add_comm] using add_le_add_right (hd v b c hcb) eps

/-- A strict cost comparison survives a sufficiently small discrete metric
perturbation. This produces a genuine metric and a positive denominator. -/
theorem exists_positive_metric_witness (E : Election) (D : Lottery E.candidateCount)
    (d : E.Metric) (hd : E.Consistent d) (a : E.Candidate) (K : ℝ)
    (hstrict : K * E.candidateCost d a < E.lotteryCost d D) :
    ∃ m : MetricSpace E.Point, E.Consistent m.toPseudoMetricSpace ∧
      0 < E.candidateCost m.toPseudoMetricSpace a ∧
      K * E.candidateCost m.toPseudoMetricSpace a < E.lotteryCost m.toPseudoMetricSpace D := by
  let gap := E.lotteryCost d D - K * E.candidateCost d a
  have hgap : 0 < gap := sub_pos.mpr hstrict
  have hden : 0 < 2 * (|K| + 1) := by positivity
  let eps := gap / (2 * (|K| + 1))
  have heps : 0 < eps := div_pos hgap hden
  have heq : eps * (2 * (|K| + 1)) = gap := div_mul_cancel₀ _ (ne_of_gt hden)
  refine ⟨separatedMetricSpace d eps heps, E.consistent_separated d hd eps heps, ?_, ?_⟩
  · rw [E.candidateCost_separated d eps heps]
    exact add_pos_of_nonneg_of_pos (E.candidateCost_nonneg d a) heps
  · rw [E.candidateCost_separated d eps heps, E.lotteryCost_separated d eps heps]
    have hmul := mul_le_mul_of_nonneg_right (le_abs_self K) heps.le
    dsimp [gap] at heq
    nlinarith only [heq, hmul, heps, mul_nonneg (abs_nonneg K) heps.le]

end Election

/-- The concrete positive-cost witness notion is exactly failure of the
universal cost bound. It does not lose zero-optimum counterexamples. -/
theorem witnessAbove_iff_not_universalBound (g : ℝ → ℝ) (K : ℝ) :
    WitnessAbove g K ↔ ¬ UniversalBound g K := by
  constructor
  · exact witnessAbove_not_universalBound g K
  · intro h
    unfold UniversalBound at h
    push Not at h
    obtain ⟨E, D, hstable, d, hd, a, hstrict⟩ := h
    obtain ⟨m, hm, hpos, hcost⟩ := E.exists_positive_metric_witness D d hd a K hstrict
    exact ⟨E, D, hstable, m.toPseudoMetricSpace, hm, a, hpos, hcost⟩

end OptimalG
