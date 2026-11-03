import OptimalG.ElectionThresholds
import OptimalG.AveragedVerifier
import OptimalG.ZeroLowMass
import OptimalG.MetricReduction

/-!
# The finite-election verifier lemma

The four functional inequalities imply the universal metric-distortion bound.
All slices are constructed from the original finite election, including candidates
of zero lottery mass. The functions of mass need no analytic regularity.
-/
namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

namespace Election

theorem voterWeight_pos (E : Election) (v : E.Voter) : 0 < E.voterWeight v := by
  exact one_div_pos.mpr (Nat.cast_pos.mpr E.voters_pos)

/-- The complete threshold integration step for actual finite elections. -/
theorem runningMin_le_of_sliceBounds (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (a : E.Candidate) (hrho : ∀ b, 0 ≤ rho b) (ha : rho a = 0)
    (lam : ℝ) (hlam : 0 ≤ lam) (W : ℝ → ℝ) (L : E.Voter → ℝ → ℝ)
    (hL : ∀ v x y, IntervalIntegrable (L v) volume x y)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, 0 ≤ W z)
    (hoffset : ∀ t, 0 ≤ t → expectation E.voterWeight (fun v => E.sliceWidth D rho v t) ≤
      expectation E.voterWeight (fun v => L v t))
    (hfirst : ∀ v t, 0 ≤ t → L v t ≤ lam - W (E.sliceWidth D rho v t))
    (hsecond : ∀ v t, 0 ≤ t → ∀ z, E.sliceRight D rho v t ≤ z → z ≤ E.leftRank D v a →
      L v t ≤ W z - W (E.sliceWidth D rho v t)) :
    expectation E.voterWeight (fun v => expectation D.weight (runningMin (E.ordinalRank v) rho)) ≤
      lam * expectation E.voterWeight (fun v => maximumGap (E.ordinalRank v) rho) := by
  let X := ∑ b, rho b
  have hX : 0 ≤ X := Finset.sum_nonneg (fun b _ => hrho b)
  have hrX (b : E.Candidate) : rho b ≤ X :=
    Finset.single_le_sum (fun b _ => hrho b) (Finset.mem_univ b)
  let q := E.sliceWidth D rho
  let delta := fun v => maximumGap (E.ordinalRank v) rho
  let F := fun v => extendedPotential W (q v) lam
  have hh := averaged_slice_bound E.voterWeight delta q L F X lam E.voterWeight_nonneg
    (fun v => maximumGap_nonneg (E.ordinalRank v) rho) hX hlam
    (fun v => E.sliceWidth_integrable D rho v 0 X) (fun v => hL v 0 X)
    (fun v => E.slice_extendedPotential_integrable D rho v W lam (-delta v) X)
    (fun v t ht => by simp [F, extendedPotential, ht])
    (fun v t ht => by
      simp only [F, extendedPotential, if_neg (not_lt.mpr ht)]
      exact hW _ (E.sliceWidth_mem_Icc D rho v t))
    (fun t ht => hoffset t ht.1) (by
      intro v t ht
      apply slice_bound_to_difference (L v) W (q v) (E.sliceRight D rho v) lam (delta v)
        (E.leftRank D v a) t ht.1 (hfirst v t ht.1) (hsecond v t ht.1)
      · exact E.sliceWidth_le_leftRank D rho a ha v
      · intro r _; exact E.slice_separation D rho v r)
  simpa only [q, E.slice_layer_cake D rho hrho X hrX] using hh

noncomputable def correctedSlice (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (a : E.Candidate) (phi : ℝ → ℝ) (lam : ℝ)
    (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ) (v : E.Voter) (t : ℝ) : ℝ :=
  E.sliceWidth D rho v t + beta (E.sliceMass D rho t) * E.sliceScore D rho phi v t +
    sliceCorrection E.voterWeight (fun u => E.leftRank D u a < lam)
      (fun u => phi (E.leftRank D u a)) (fun u => corr (E.sliceMass D rho t) (E.leftRank D u a)) v

theorem correctedSlice_integrable (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (a : E.Candidate) (phi : ℝ → ℝ) (lam : ℝ)
    (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ) (v : E.Voter) (x y : ℝ) :
    IntervalIntegrable (E.correctedSlice D rho a phi lam beta corr v) volume x y :=
  thresholdSet_function_integrable rho
    (fun S => rankCut (E.rankWeights D v) (prefixBoundary (E.rankSet S v)) +
      beta (∑ b ∈ S, D.weight b) * E.blockScore phi D S v +
      sliceCorrection E.voterWeight (fun u => E.leftRank D u a < lam)
        (fun u => phi (E.leftRank D u a))
        (fun u => corr (∑ b ∈ S, D.weight b) (E.leftRank D u a)) v) x y

end Election

/-- Lemma 5.1, with coefficients extended to include the endpoint masses. -/
theorem verifier_runningMinBound {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Icc 0 1) phi lam beta corr) :
    RunningMinBound (normalizedActivation phi) lam := by
  intro E D hstable a rho hrho ha
  let s := fun v => E.leftRank D v a
  have hs : ∀ v, s v ∈ Icc (0 : ℝ) 1 := fun v => E.leftRank_mem_Icc D v a
  have hmean := E.stable_left_score_nonnegative phi D h.continuous h.decreasing
    h.at_one h.integral_zero hstable a
  have hA0 := lowScoreMass_nonneg E.voterWeight s h E.voterWeight_nonneg hs
  rcases eq_or_lt_of_le hA0 with hAz | hA
  · have heq := all_ranks_equal_of_zero_lowScoreMass E.voterWeight s h E.voterWeight_pos hs hmean hAz.symm
    let L := fun v t => E.sliceWidth D rho v t + beta (E.sliceMass D rho t) * E.sliceScore D rho phi v t
    apply E.runningMin_le_of_sliceBounds D rho a hrho ha lam h.lam_pos.le (fun _ => 0) L
    · intro v x y
      exact thresholdSet_function_integrable rho
        (fun S => rankCut (E.rankWeights D v) (prefixBoundary (E.rankSet S v)) +
          beta (∑ b ∈ S, D.weight b) * E.blockScore phi D S v) x y
    · intro z hz; rfl
    · intro t ht
      change _ ≤ expectation E.voterWeight (fun v => E.sliceWidth D rho v t +
        beta (E.sliceMass D rho t) * E.sliceScore D rho phi v t)
      rw [expectation_add, expectation_smul, E.sliceScore_mean_zero D rho h hstable t]
      simp
    · intro v t ht
      simp only [sub_zero]
      apply zeroLow_offset_first h beta corr hv (E.sliceMass_mem_Icc D rho t)
        (E.sliceWidth_mem_Icc D rho v t).1 (E.sliceWidth_le_mass D rho v t)
      · simpa only [← heq v] using E.sliceWidth_le_leftRank D rho a ha v t ht
      · exact E.slice_packingDelta D rho phi h.continuous h.decreasing.antitoneOn h.integral_zero v t
    · intro v t ht z hz hzs
      simp only [sub_self]
      apply zeroLow_offset_second h beta corr hv (E.sliceMass_mem_Icc D rho t)
        (E.sliceWidth_mem_Icc D rho v t).1 (E.sliceWidth_le_mass D rho v t)
        ((E.sliceMass_le_right D rho v t).trans hz)
      · simpa only [← heq v] using hzs
      · exact E.slice_packingK D rho phi h.continuous h.decreasing.antitoneOn v t z hz
          (hzs.trans (hs v).2)
  · apply E.runningMin_le_of_sliceBounds D rho a hrho ha lam h.lam_pos.le
      (averagedRankPotential E.voterWeight s phi lam) (E.correctedSlice D rho a phi lam beta corr)
    · exact E.correctedSlice_integrable D rho a phi lam beta corr
    · intro z hz
      exact averagedRankPotential_nonneg E.voterWeight s h E.voterWeight_nonneg hs hA hz
    · intro t ht
      exact expected_slice_le_offset E.voterWeight (fun v => s v < lam)
        (fun v => phi (s v)) (fun v => corr (E.sliceMass D rho t) (s v))
        (fun v => E.sliceWidth D rho v t) (fun v => E.sliceScore D rho phi v t)
        (beta (E.sliceMass D rho t)) E.voterWeight_nonneg
        (fun v hl => hv.corr_nonneg _ (E.sliceMass_mem_Icc D rho t) _ ⟨(hs v).1, hl⟩)
        hA hmean (E.sliceScore_mean_zero D rho h hstable t)
    · intro v t ht
      exact offset_first E.voterWeight s h E.voterWeight_nonneg hs hA beta corr hv v
        _ _ _ (E.sliceMass_mem_Icc D rho t) (E.sliceWidth_mem_Icc D rho v t).1
        (E.sliceWidth_le_mass D rho v t) (E.sliceWidth_le_leftRank D rho a ha v t ht)
        (E.slice_packingDelta D rho phi h.continuous h.decreasing.antitoneOn h.integral_zero v t)
    · intro v t ht z hz hzs
      exact offset_second E.voterWeight s h E.voterWeight_nonneg hs hA beta corr hv v
        _ _ z _ (E.sliceMass_mem_Icc D rho t) (E.sliceWidth_mem_Icc D rho v t).1
        (E.sliceWidth_le_mass D rho v t) ((E.sliceMass_le_right D rho v t).trans hz) hzs
        (E.slice_packingK D rho phi h.continuous h.decreasing.antitoneOn v t z hz
          (hzs.trans (hs v).2))
        (E.slice_packingK D rho phi h.continuous h.decreasing.antitoneOn v t (s v)
          (hz.trans hzs) (hs v).2)

/-- The universal metric-distortion conclusion for the original open-mass hypotheses. -/
theorem verifier_universalBound {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Ioo 0 1) phi lam beta corr) :
    UniversalBound (normalizedActivation phi) (1 + 2 * lam) := by
  obtain ⟨b, c, hbc⟩ := verifier_extend_endpoints h beta corr hv
  exact runningMinBound_implies_universalBound _ _ h.lam_pos.le (verifier_runningMinBound h b c hbc)

theorem verifier_maximumDistortion {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Ioo 0 1) phi lam beta corr) :
    maximumDistortion (normalizedActivation phi) ≤ ENNReal.ofReal (1 + 2 * lam) :=
  (maximumDistortion_le_iff _ _ (by linarith [h.lam_pos])).mpr (verifier_universalBound h beta corr hv)

end OptimalG
