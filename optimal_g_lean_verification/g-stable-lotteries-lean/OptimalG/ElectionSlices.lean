import OptimalG.CenteredStability
import OptimalG.RankPacking
import OptimalG.ThresholdIntegrability

/-! Reindexing the actual election by each voter's rank order. -/
namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

theorem runningMin_reindex {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) (rank : B → ℕ) (rho : B → ℝ) (a : A) :
    runningMin (fun i => rank (e i)) (fun i => rho (e i)) a =
      runningMin rank rho (e a) := by
  apply le_antisymm
  · obtain ⟨b, hb, heq⟩ := runningMin_attained rank rho (e a)
    rw [heq]
    simpa only [e.apply_symm_apply] using
      runningMin_le_of_rank_le (fun i => rank (e i)) (fun i => rho (e i))
        a (e.symm b) (by simpa only [e.apply_symm_apply] using hb)
  · obtain ⟨i, hi, heq⟩ := runningMin_attained (fun i => rank (e i)) (fun i => rho (e i)) a
    rw [heq]
    exact runningMin_le_of_rank_le rank rho (e a) (e i) hi

theorem maximumGap_reindex {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) (rank : B → ℕ) (rho : B → ℝ) :
    maximumGap (fun i => rank (e i)) (fun i => rho (e i)) = maximumGap rank rho := by
  apply le_antisymm
  · obtain ⟨a, ha⟩ := maximumGap_attained (fun i => rank (e i)) (fun i => rho (e i))
    rw [ha, runningMin_reindex]
    exact le_maximumGap rank rho (e a)
  · obtain ⟨b, hb⟩ := maximumGap_attained rank rho
    rw [hb]
    have hh := le_maximumGap (fun i => rank (e i)) (fun i => rho (e i)) (e.symm b)
    simpa only [runningMin_reindex, e.apply_symm_apply] using hh

namespace Election
noncomputable abbrev rankWeights (E : Election) (D : Lottery E.candidateCount)
    (v : E.Voter) (i : Fin E.candidateCount) : ℝ := D.weight (E.order v i)
noncomputable abbrev rankHeights (E : Election) (rho : E.Candidate → ℝ)
    (v : E.Voter) (i : Fin E.candidateCount) : ℝ := rho (E.order v i)
noncomputable def rankSet (E : Election) (S : Finset E.Candidate) (v : E.Voter) :
    Finset (Fin E.candidateCount) := S.map (E.order v).symm.toEmbedding

theorem rankWeights_nonneg (E : Election) (D : Lottery E.candidateCount) (v : E.Voter)
    (i : Fin E.candidateCount) : 0 ≤ E.rankWeights D v i := D.nonneg _
theorem rankWeights_total (E : Election) (D : Lottery E.candidateCount) (v : E.Voter) :
    ∑ i, E.rankWeights D v i = 1 := by
  simpa only [rankWeights, Equiv.sum_comp] using D.total

theorem mass_rankSet (E : Election) (D : Lottery E.candidateCount)
    (S : Finset E.Candidate) (v : E.Voter) :
    (∑ i ∈ E.rankSet S v, E.rankWeights D v i) = ∑ a ∈ S, D.weight a := by
  classical
  simp [rankSet, rankWeights, Finset.sum_map]

theorem blockScore_rankSet (E : Election) (D : Lottery E.candidateCount)
    (S : Finset E.Candidate) (phi : ℝ → ℝ) (v : E.Voter) :
    E.blockScore phi D S v = centeredBlock (E.rankWeights D v) (E.rankSet S v) phi := by
  classical
  unfold blockScore centeredBlock
  congr 1
  rw [rankSet, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a _
  have hh := mass_mul_rankActivation phi (E.rankWeights D v) ((E.order v).symm a)
  dsimp [rankWeights, activation, orderedActivation] at *
  simpa only [Equiv.apply_symm_apply] using hh

theorem runningMin_rankHeights (E : Election) (rho : E.Candidate → ℝ)
    (v : E.Voter) (i : Fin E.candidateCount) :
    runningMin (fun j : Fin E.candidateCount => j.val) (E.rankHeights rho v) i =
      runningMin (E.ordinalRank v) rho (E.order v i) := by
  simpa only [ordinalRank, Equiv.symm_apply_apply] using
    runningMin_reindex (E.order v) (E.ordinalRank v) rho i

theorem maximumGap_rankHeights (E : Election) (rho : E.Candidate → ℝ) (v : E.Voter) :
    maximumGap (fun j : Fin E.candidateCount => j.val) (E.rankHeights rho v) =
      maximumGap (E.ordinalRank v) rho := by
  simpa only [ordinalRank, Equiv.symm_apply_apply] using
    maximumGap_reindex (E.order v) (E.ordinalRank v) rho

theorem numerator_rankHeights (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) :
    expectation (E.rankWeights D v)
      (runningMin (fun j : Fin E.candidateCount => j.val) (E.rankHeights rho v)) =
      expectation D.weight (runningMin (E.ordinalRank v) rho) := by
  simp only [expectation, runningMin_rankHeights, rankWeights]
  exact Equiv.sum_comp (E.order v) (fun a => D.weight a * runningMin (E.ordinalRank v) rho a)

theorem thresholdSet_rankHeights (E : Election) (rho : E.Candidate → ℝ)
    (v : E.Voter) (t : ℝ) :
    thresholdSet (E.rankHeights rho v) t = E.rankSet (thresholdSet rho t) v := by
  classical
  ext i
  simp [thresholdSet, rankHeights, rankSet]

end Election
end OptimalG
