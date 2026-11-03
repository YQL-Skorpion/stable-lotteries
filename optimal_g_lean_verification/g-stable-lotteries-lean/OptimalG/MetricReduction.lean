import OptimalG.Election
import OptimalG.BiasedMetric

/-! Full biased-metric equivalence for the actual finite-election distortion. -/

namespace OptimalG

def RunningMinBound (g : ℝ → ℝ) (lam : ℝ) : Prop :=
  ∀ (E : Election) (D : Lottery E.candidateCount), E.Stable g D →
    ∀ (a : E.Candidate) (rho : E.Candidate → ℝ),
      (∀ b, 0 ≤ rho b) → rho a = 0 →
        expectation E.voterWeight (fun v => expectation D.weight (runningMin (E.ordinalRank v) rho)) ≤
          lam * expectation E.voterWeight (fun v => maximumGap (E.ordinalRank v) rho)

theorem runningMin_violation_witness (g : ℝ → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (E : Election) (D : Lottery E.candidateCount) (hs : E.Stable g D)
    (a : E.Candidate) (rho : E.Candidate → ℝ) (hrho : ∀ b, 0 ≤ rho b) (ha : rho a = 0)
    (hv : lam * expectation E.voterWeight (fun v => maximumGap (E.ordinalRank v) rho) <
      expectation E.voterWeight (fun v => expectation D.weight (runningMin (E.ordinalRank v) rho))) :
    WitnessAbove g (1 + 2 * lam) := by
  obtain ⟨m, hconsistent, _hoptimal, hpositive, hratio⟩ :=
    exists_metric_of_strict_runningMin_violation E.ordinalRank rho E.voterWeight D.weight lam
      hrho E.voterWeight_nonneg E.voterWeight_total D.total hlam a ha hv
  refine ⟨E, D, hs, m.toPseudoMetricSpace, hconsistent, a, hpositive, ?_⟩
  rw [E.lotteryCost_eq_voter_average]
  exact (lt_div_iff₀ hpositive).mp hratio

theorem runningMinBound_implies_universalBound (g : ℝ → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam) (hbound : RunningMinBound g lam) :
    UniversalBound g (1 + 2 * lam) := by
  intro E D hs d hc a
  letI := d
  rw [E.lotteryCost_eq_voter_average]
  apply metric_distortion_upper_bound
    (fun v : E.Voter => (Sum.inl v : E.Point))
    (fun b : E.Candidate => (Sum.inr b : E.Point))
    E.ordinalRank E.voterWeight D.weight a lam E.voterWeight_nonneg D.nonneg D.total hlam hc
  exact hbound E D hs a (fun b => dist (Sum.inr a : E.Point) (Sum.inr b))
    (fun _ => dist_nonneg) (dist_self _)

theorem universalBound_iff_runningMinBound (g : ℝ → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) :
    UniversalBound g (1 + 2 * lam) ↔ RunningMinBound g lam := by
  constructor
  · intro hbound E D hs a rho hrho ha
    by_contra h
    have hw := runningMin_violation_witness g lam hlam E D hs a rho hrho ha (lt_of_not_ge h)
    exact witnessAbove_not_universalBound g (1 + 2 * lam) hw hbound
  · exact runningMinBound_implies_universalBound g lam hlam

/-- Lemma 2.4, with the supremum over all actual finite stable elections. -/
theorem maximumDistortion_iff_runningMinBound (g : ℝ → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) :
    maximumDistortion g ≤ ENNReal.ofReal (1 + 2 * lam) ↔ RunningMinBound g lam := by
  rw [maximumDistortion_le_iff g (1 + 2 * lam) (by linarith)]
  exact universalBound_iff_runningMinBound g lam hlam

end OptimalG
