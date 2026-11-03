import OptimalG.Election
import OptimalG.Activation

/-! Exact consequences of stability for the normalized centered curve. -/

namespace OptimalG

open Set MeasureTheory
open scoped BigOperators

theorem rankIntegrand_integrable {n : ℕ} (f : ℝ → ℝ) (D : Fin n → ℝ)
    (hf : ContinuousOn f (Icc 0 1)) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (i : Fin n) :
    IntervalIntegrable (fun u : ℝ => f (rankCut D i.val + u * D i)) volume 0 1 := by
  have hcoord : Continuous (fun u : ℝ => rankCut D i.val + u * D i) := by fun_prop
  apply (hf.comp hcoord.continuousOn ?_).intervalIntegrable_of_Icc (by norm_num)
  intro u hu
  have hr := rankCut_mem_Icc D hD hDsum i.val
  have hrend := (rankCut_mem_Icc D hD hDsum (i.val + 1)).2
  rw [rankCut_succ] at hrend
  constructor
  · exact add_nonneg hr.1 (mul_nonneg hu.1 (hD i))
  · have hmul := mul_le_mul_of_nonneg_right hu.2 (hD i)
    linarith

theorem rankActivation_normalized {n : ℕ} (phi : ℝ → ℝ) (D : Fin n → ℝ)
    (hphi : ContinuousOn phi (Icc 0 1)) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (i : Fin n) :
    rankActivation (normalizedActivation phi) D i =
      (phi 0 - rankActivation phi D i) / (1 + phi 0) := by
  unfold rankActivation normalizedActivation
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub intervalIntegrable_const
      (rankIntegrand_integrable phi D hphi hD hDsum i)]
  simp

theorem orderedActivation_normalized {C : Type*} [Fintype C] {n : ℕ}
    (phi : ℝ → ℝ) (D : C → ℝ) (order : Fin n ≃ C)
    (hphi : ContinuousOn phi (Icc 0 1)) (hD : ∀ a, 0 ≤ D a) (hDsum : ∑ a, D a = 1)
    (a : C) :
    orderedActivation (normalizedActivation phi) D order a =
      (phi 0 - orderedActivation phi D order a) / (1 + phi 0) := by
  have hsum : ∑ i, D (order i) = 1 := by simpa only [Equiv.sum_comp] using hDsum
  exact rankActivation_normalized phi (fun i => D (order i)) hphi
    (fun i => hD (order i)) hsum (order.symm a)

theorem expectation_sub_const_div {V : Type*} [Fintype V]
    (w f : V → ℝ) (c d : ℝ) (hw : ∑ v, w v = 1) :
    expectation w (fun v => (c - f v) / d) = (c - expectation w f) / d := by
  unfold expectation
  simp_rw [← mul_div_assoc, mul_sub]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul]

namespace Election

theorem mean_normalized_activation (E : Election) (phi : ℝ → ℝ)
    (D : Lottery E.candidateCount) (hphi : ContinuousOn phi (Icc 0 1)) (a : E.Candidate) :
    expectation E.voterWeight (fun v => E.activation (normalizedActivation phi) D v a) =
      (phi 0 - expectation E.voterWeight (fun v => E.activation phi D v a)) / (1 + phi 0) := by
  simp only [activation, orderedActivation_normalized phi D.weight _ hphi D.nonneg D.total]
  exact expectation_sub_const_div _ _ _ _ E.voterWeight_total

theorem stable_centered_nonnegative (E : Election) (phi : ℝ → ℝ)
    (D : Lottery E.candidateCount) (hphi : ContinuousOn phi (Icc 0 1))
    (hanti : StrictAntiOn phi (Icc 0 1)) (hend : phi 1 = -1)
    (hzero : (∫ r in (0 : ℝ)..1, phi r) = 0)
    (hs : E.Stable (normalizedActivation phi) D) (a : E.Candidate) :
    0 ≤ expectation E.voterWeight (fun v => E.activation phi D v a) := by
  have h := hs a
  rw [mean_normalized_activation E phi D hphi a,
    normalizedActivation_integral hphi hzero] at h
  have hh := (div_le_div_iff_of_pos_right (normalization_denominator_pos hanti hend)).mp h
  linarith

theorem stable_centered_supported (E : Election) (phi : ℝ → ℝ)
    (D : Lottery E.candidateCount) (hphi : ContinuousOn phi (Icc 0 1))
    (hanti : StrictAntiOn phi (Icc 0 1)) (hend : phi 1 = -1)
    (hzero : (∫ r in (0 : ℝ)..1, phi r) = 0)
    (hs : E.Stable (normalizedActivation phi) D) (a : E.Candidate) (ha : 0 < D.weight a) :
    expectation E.voterWeight (fun v => E.activation phi D v a) = 0 := by
  have h := E.supported_stationarity (normalizedActivation phi) D
    (normalizedActivation_continuousOn hphi) hs a ha
  rw [mean_normalized_activation E phi D hphi a,
    normalizedActivation_integral hphi hzero] at h
  have hden := ne_of_gt (normalization_denominator_pos hanti hend)
  have hh := (div_left_inj' hden).mp h
  linarith

noncomputable def leftRank (E : Election) (D : Lottery E.candidateCount)
    (v : E.Voter) (a : E.Candidate) : ℝ :=
  rankCut (fun i => D.weight (E.order v i)) ((E.order v).symm a).val

theorem leftRank_mem_Icc (E : Election) (D : Lottery E.candidateCount)
    (v : E.Voter) (a : E.Candidate) : E.leftRank D v a ∈ Icc 0 1 := by
  apply rankCut_mem_Icc _ (fun i => D.nonneg (E.order v i))
  simpa only [Equiv.sum_comp] using D.total

/-- The left endpoint of a decreasing curve dominates its candidate-interval average. -/
theorem centered_average_le_left (E : Election) (phi : ℝ → ℝ)
    (D : Lottery E.candidateCount) (hphi : ContinuousOn phi (Icc 0 1))
    (hanti : AntitoneOn phi (Icc 0 1)) (v : E.Voter) (a : E.Candidate) :
    E.activation phi D v a ≤ phi (E.leftRank D v a) := by
  let F : Fin E.candidateCount → ℝ := fun i => D.weight (E.order v i)
  let i := (E.order v).symm a
  have hF : ∀ j, 0 ≤ F j := fun j => D.nonneg (E.order v j)
  have hsum : ∑ j, F j = 1 := by simpa only [F, Equiv.sum_comp] using D.total
  have hleft := rankCut_mem_Icc F hF hsum i.val
  have hendcut := (rankCut_mem_Icc F hF hsum (i.val + 1)).2
  rw [rankCut_succ] at hendcut
  have h := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) (by norm_num)
    (rankIntegrand_integrable phi F hphi hF hsum i)
    (intervalIntegrable_const (c := phi (rankCut F i.val))) (fun u hu => ?_)
  · simpa only [intervalIntegral.integral_const, sub_zero, one_smul, activation,
      orderedActivation, rankActivation, leftRank, F, i] using h
  · have hmul := mul_nonneg hu.1 (hF i)
    have hmul1 := mul_le_mul_of_nonneg_right hu.2 (hF i)
    apply hanti hleft ⟨by linarith [hleft.1], by linarith⟩
    linarith

/-- Equation (5.4), derived from actual stability rather than assumed. -/
theorem stable_left_score_nonnegative (E : Election) (phi : ℝ → ℝ)
    (D : Lottery E.candidateCount) (hphi : ContinuousOn phi (Icc 0 1))
    (hanti : StrictAntiOn phi (Icc 0 1)) (hend : phi 1 = -1)
    (hzero : (∫ r in (0 : ℝ)..1, phi r) = 0)
    (hs : E.Stable (normalizedActivation phi) D) (a : E.Candidate) :
    0 ≤ expectation E.voterWeight (fun v => phi (E.leftRank D v a)) := by
  exact le_trans (E.stable_centered_nonnegative phi D hphi hanti hend hzero hs a)
    (expectation_mono E.voterWeight_nonneg
      (fun v => E.centered_average_le_left phi D hphi hanti.antitoneOn v a))

/-- Centered activation of a candidate set, using its actual candidate averages. -/
noncomputable def blockScore (E : Election) (phi : ℝ → ℝ) (D : Lottery E.candidateCount)
    (S : Finset E.Candidate) (v : E.Voter) : ℝ :=
  -(∑ a ∈ S, D.weight a * E.activation phi D v a)

/-- Equation (5.3), including candidates of zero lottery mass. -/
theorem stable_blockScore_zero (E : Election) (phi : ℝ → ℝ)
    (D : Lottery E.candidateCount) (hphi : ContinuousOn phi (Icc 0 1))
    (hanti : StrictAntiOn phi (Icc 0 1)) (hend : phi 1 = -1)
    (hzero : (∫ r in (0 : ℝ)..1, phi r) = 0)
    (hs : E.Stable (normalizedActivation phi) D) (S : Finset E.Candidate) :
    expectation E.voterWeight (E.blockScore phi D S) = 0 := by
  classical
  have heq : expectation E.voterWeight (E.blockScore phi D S) =
      -(∑ a ∈ S, D.weight a * expectation E.voterWeight (fun v => E.activation phi D v a)) := by
    simp only [expectation, blockScore, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [heq, neg_eq_zero]
  apply Finset.sum_eq_zero
  intro a _
  rcases eq_or_lt_of_le (D.nonneg a) with ha | ha
  · rw [← ha, zero_mul]
  · rw [E.stable_centered_supported phi D hphi hanti hend hzero hs a ha, mul_zero]

end Election
end OptimalG
