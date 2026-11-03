import OptimalG.ElectionSlices
import OptimalG.VerifierConditions

/-! All geometric and integral facts about slices of actual finite elections. -/
namespace OptimalG.Election
open Set MeasureTheory
open scoped BigOperators

noncomputable def sliceMass (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (t : ℝ) : ℝ := ∑ a ∈ thresholdSet rho t, D.weight a
noncomputable def sliceWidth (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) : ℝ :=
  rankCut (E.rankWeights D v) (prefixBoundary (E.rankSet (thresholdSet rho t) v))
noncomputable def sliceRight (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) : ℝ :=
  rankCut (E.rankWeights D v) (lastIndex (E.rankSet (thresholdSet rho t) v))
noncomputable def sliceScore (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (phi : ℝ → ℝ) (v : E.Voter) (t : ℝ) : ℝ :=
  E.blockScore phi D (thresholdSet rho t) v

theorem sliceWidth_eq_threshold (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) :
    E.sliceWidth D rho v t = thresholdWidth (E.rankWeights D v) (E.rankHeights rho v) t := by
  rw [thresholdWidth, E.thresholdSet_rankHeights]; rfl

theorem sliceRight_eq_threshold (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) :
    E.sliceRight D rho v t = thresholdRight (E.rankWeights D v) (E.rankHeights rho v) t := by
  rw [thresholdRight, E.thresholdSet_rankHeights]; rfl

theorem sliceMass_mem_Icc (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (t : ℝ) : E.sliceMass D rho t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg (fun a _ => D.nonneg a)
  · calc
      _ ≤ ∑ a, D.weight a := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun a _ _ => D.nonneg a)
      _ = 1 := D.total

theorem sliceWidth_mem_Icc (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) : E.sliceWidth D rho v t ∈ Icc (0 : ℝ) 1 :=
  rankCut_mem_Icc _ (E.rankWeights_nonneg D v) (E.rankWeights_total D v) _

theorem sliceRight_mem_Icc (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) : E.sliceRight D rho v t ∈ Icc (0 : ℝ) 1 :=
  rankCut_mem_Icc _ (E.rankWeights_nonneg D v) (E.rankWeights_total D v) _

theorem sliceWidth_le_mass (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) :
    E.sliceWidth D rho v t ≤ E.sliceMass D rho t := by
  have hh := prefixCut_le_mass (E.rankWeights D v) (E.rankWeights_nonneg D v)
    (E.rankSet (thresholdSet rho t) v)
  rwa [E.mass_rankSet] at hh

theorem sliceMass_le_right (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) :
    E.sliceMass D rho t ≤ E.sliceRight D rho v t := by
  have hh := mass_le_lastCut (E.rankWeights D v) (E.rankWeights_nonneg D v)
    (E.rankSet (thresholdSet rho t) v)
  rwa [E.mass_rankSet] at hh

theorem sliceWidth_le_leftRank (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (a : E.Candidate) (ha : rho a = 0)
    (v : E.Voter) (t : ℝ) (ht : 0 ≤ t) : E.sliceWidth D rho v t ≤ E.leftRank D v a := by
  rw [E.sliceWidth_eq_threshold]
  exact thresholdWidth_le_referenceRank (E.rankWeights D v) (E.rankHeights rho v)
    (E.rankWeights_nonneg D v) ((E.order v).symm a) (by simpa only [rankHeights, Equiv.apply_symm_apply] using ha) t ht

theorem slice_separation (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) :
    E.sliceRight D rho v (t + maximumGap (E.ordinalRank v) rho) ≤ E.sliceWidth D rho v t := by
  rw [E.sliceWidth_eq_threshold, E.sliceRight_eq_threshold, ← E.maximumGap_rankHeights rho v]
  exact threshold_separation _ _ (E.rankWeights_nonneg D v) t

theorem slice_layer_cake (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (hrho : ∀ a, 0 ≤ rho a) (X : ℝ) (hX : ∀ a, rho a ≤ X)
    (v : E.Voter) : (∫ t in (0 : ℝ)..X, E.sliceWidth D rho v t) =
      expectation D.weight (runningMin (E.ordinalRank v) rho) := by
  simp_rw [E.sliceWidth_eq_threshold]
  rw [(threshold_layer_cake (E.rankWeights D v) (E.rankHeights rho v) X
    (fun i => hrho (E.order v i)) (fun i => hX (E.order v i))).2]
  exact E.numerator_rankHeights D rho v

theorem slice_packingK (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (phi : ℝ → ℝ)
    (hphi : ContinuousOn phi (Icc 0 1)) (hanti : AntitoneOn phi (Icc 0 1))
    (v : E.Voter) (t z : ℝ) (hz : E.sliceRight D rho v t ≤ z) (hz1 : z ≤ 1) :
    E.sliceScore D rho phi v t ≤ packingK phi (E.sliceMass D rho t) (E.sliceWidth D rho v t) z := by
  rw [sliceScore, E.blockScore_rankSet]
  exact centeredBlock_packing (E.rankWeights D v) (E.rankWeights_nonneg D v)
    (E.rankWeights_total D v) (E.rankSet (thresholdSet rho t) v) phi hphi hanti
    (E.sliceMass D rho t) (E.sliceWidth D rho v t) z
    (E.mass_rankSet D (thresholdSet rho t) v).symm rfl hz hz1

theorem slice_packingDelta (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (phi : ℝ → ℝ)
    (hphi : ContinuousOn phi (Icc 0 1)) (hanti : AntitoneOn phi (Icc 0 1))
    (hzero : (∫ r in (0 : ℝ)..1, phi r) = 0) (v : E.Voter) (t : ℝ) :
    E.sliceScore D rho phi v t ≤ packingDelta phi (E.sliceMass D rho t) (E.sliceWidth D rho v t) := by
  have hh := E.slice_packingK D rho phi hphi hanti v t 1 (E.sliceRight_mem_Icc D rho v t).2 le_rfl
  simpa only [packingK, packingDelta, curvePrimitive, hzero, sub_zero] using hh

theorem sliceScore_mean_zero (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (hstable : E.Stable (normalizedActivation phi) D) (t : ℝ) :
    expectation E.voterWeight (fun v => E.sliceScore D rho phi v t) = 0 :=
  E.stable_blockScore_zero phi D h.continuous h.decreasing h.at_one h.integral_zero hstable _

theorem sliceWidth_integrable (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (a b : ℝ) :
    IntervalIntegrable (E.sliceWidth D rho v) volume a b :=
  thresholdSet_function_integrable rho
    (fun S => rankCut (E.rankWeights D v) (prefixBoundary (E.rankSet S v))) a b

theorem slice_extendedPotential_integrable (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (W : ℝ → ℝ) (lam a b : ℝ) :
    IntervalIntegrable (extendedPotential W (E.sliceWidth D rho v) lam) volume a b :=
  extendedThreshold_integrable rho
    (fun S => W (rankCut (E.rankWeights D v) (prefixBoundary (E.rankSet S v)))) lam a b

end OptimalG.Election
