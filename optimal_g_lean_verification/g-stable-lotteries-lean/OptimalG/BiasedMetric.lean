import OptimalG.Finite
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Realizing the biased pseudometric

The prescribed candidate and voter distances of Definition 2.3 extend to an
actual pseudometric on `V ⊕ C`. We use an explicit finite-dimensional embedding:
a candidate is its candidate-distance profile and a voter is its prescribed
voter-to-candidate profile. The sup metric preserves all prescribed distances
because these profiles satisfy the two one-point-extension triangle inequalities.
This replaces the manuscript's shortest-path extension with an equivalent
existence proof and imposes no positivity or distinctness beyond a pseudometric.
-/

namespace OptimalG

open scoped BigOperators

section RunningMinimum

variable {C : Type*} [Fintype C] [Nonempty C]

theorem runningMin_nonneg (rank : C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (b : C) : 0 ≤ runningMin rank rho b := by
  apply Finset.le_inf'
  intro c _
  split_ifs
  · exact hrho c
  · exact hrho b

theorem runningMin_le_of_rank_le (rank : C → ℕ) (rho : C → ℝ)
    (b c : C) (hcb : rank c ≤ rank b) : runningMin rank rho b ≤ rho c := by
  have h := Finset.inf'_le
    (fun a => if rank a ≤ rank b then rho a else rho b) (Finset.mem_univ c)
  simpa only [runningMin, if_pos hcb] using h

theorem runningMin_le_self (rank : C → ℕ) (rho : C → ℝ) (b : C) :
    runningMin rank rho b ≤ rho b :=
  runningMin_le_of_rank_le rank rho b b le_rfl

theorem runningMin_antitone_rank (rank : C → ℕ) (rho : C → ℝ)
    (b c : C) (hcb : rank c ≤ rank b) : runningMin rank rho b ≤ runningMin rank rho c := by
  apply Finset.le_inf'
  intro a _
  split_ifs with hac
  · exact runningMin_le_of_rank_le rank rho b a (le_trans hac hcb)
  · exact runningMin_le_of_rank_le rank rho b c hcb

theorem runningMin_at_zero (rank : C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (a : C) (ha : rho a = 0) : runningMin rank rho a = 0 := by
  apply le_antisymm
  · simpa only [ha] using runningMin_le_self rank rho a
  · exact runningMin_nonneg rank rho hrho a

theorem le_maximumGap (rank : C → ℕ) (rho : C → ℝ) (b : C) :
    rho b - runningMin rank rho b ≤ maximumGap rank rho := by
  exact Finset.le_sup' (fun c => rho c - runningMin rank rho c) (Finset.mem_univ b)

/-- The running minimum is attained at a candidate ranked no higher than b. -/
theorem runningMin_attained (rank : C → ℕ) (rho : C → ℝ) (b : C) :
    ∃ c, rank c ≤ rank b ∧ runningMin rank rho b = rho c := by
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ)
    Finset.univ_nonempty (fun c => if rank c ≤ rank b then rho c else rho b)
  by_cases hcb : rank c ≤ rank b
  · exact ⟨c, hcb, by simpa only [runningMin, if_pos hcb] using hc⟩
  · exact ⟨b, le_rfl, by simpa only [runningMin, if_neg hcb] using hc⟩

/-- The maximum drop is attained, also when all drops are zero. -/
theorem maximumGap_attained (rank : C → ℕ) (rho : C → ℝ) :
    ∃ b, maximumGap rank rho = rho b - runningMin rank rho b := by
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty (fun b => rho b - runningMin rank rho b)
  exact ⟨b, hb⟩

theorem maximumGap_nonneg (rank : C → ℕ) (rho : C → ℝ) : 0 ≤ maximumGap rank rho := by
  let b : C := Classical.arbitrary C
  exact le_trans (sub_nonneg.mpr (runningMin_le_self rank rho b)) (le_maximumGap rank rho b)

end RunningMinimum

/-- Distances between distinct candidates in the biased construction. -/
noncomputable def biasedCandidateDistance {C : Type*} (rho : C → ℝ) (a b : C) : ℝ :=
  by classical exact if a = b then 0 else max (rho a) (rho b)

@[simp] theorem biasedCandidateDistance_self {C : Type*} (rho : C → ℝ) (a : C) :
    biasedCandidateDistance rho a a = 0 := by simp [biasedCandidateDistance]

theorem biasedCandidateDistance_comm {C : Type*} (rho : C → ℝ) (a b : C) :
    biasedCandidateDistance rho a b = biasedCandidateDistance rho b a := by
  classical
  simp only [biasedCandidateDistance, eq_comm, max_comm]

theorem biasedCandidateDistance_nonneg {C : Type*} (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (a b : C) : 0 ≤ biasedCandidateDistance rho a b := by
  classical
  unfold biasedCandidateDistance
  split_ifs
  · rfl
  · exact le_trans (hrho a) (le_max_left _ _)

theorem biasedCandidateDistance_triangle {C : Type*} (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (a b c : C) :
    biasedCandidateDistance rho a c ≤ biasedCandidateDistance rho a b +
      biasedCandidateDistance rho b c := by
  classical
  by_cases hab : a = b
  · subst b
    simp
  by_cases hbc : b = c
  · subst c
    simp
  by_cases hac : a = c
  · subst c
    simp only [biasedCandidateDistance_self]
    exact add_nonneg (biasedCandidateDistance_nonneg rho hrho a b)
      (biasedCandidateDistance_nonneg rho hrho b a)
  simp only [biasedCandidateDistance, if_neg hab, if_neg hbc, if_neg hac]
  apply max_le
  · have h1 := le_max_left (rho a) (rho b)
    have h2 : 0 ≤ max (rho b) (rho c) := le_trans (hrho b) (le_max_left _ _)
    linarith
  · have h1 := le_max_right (rho b) (rho c)
    have h2 : 0 ≤ max (rho a) (rho b) := le_trans (hrho a) (le_max_left _ _)
    linarith

/-- The exact candidate-to-reference heights, including the reference itself. -/
theorem biasedCandidateDistance_from_zero {C : Type*} (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (a : C) (ha : rho a = 0) (b : C) :
    biasedCandidateDistance rho a b = rho b := by
  classical
  by_cases hab : a = b
  · subst b
    simp [ha]
  · simp [biasedCandidateDistance, hab, ha, max_eq_right (hrho b)]

/-- A general finite sup-norm realization of a one-point metric extension. -/
theorem dist_profile_eq {C : Type*} [Fintype C]
    (d : C → C → ℝ) (f : C → ℝ)
    (hself : ∀ c, d c c = 0) (hcomm : ∀ b c, d b c = d c b)
    (hf : ∀ c, 0 ≤ f c)
    (hsub : ∀ b c, f b ≤ f c + d b c)
    (hsum : ∀ b c, d b c ≤ f b + f c) (a : C) :
    dist f (d a) = f a := by
  apply le_antisymm
  · apply (dist_pi_le_iff (hf a)).mpr
    intro b
    rw [Real.dist_eq, abs_le]
    have h1 := hsub b a
    rw [hcomm b a] at h1
    have h2 := hsum a b
    constructor <;> linarith
  · have h := dist_le_pi_dist f (d a) a
    simpa only [hself a, Real.dist_eq, sub_zero, abs_of_nonneg (hf a)] using h

section Construction

variable {V C : Type*} [Fintype C] [Nonempty C]

/-- Prescribed voter-to-candidate distance. -/
noncomputable def biasedVoterDistance (rank : V → C → ℕ) (rho : C → ℝ)
    (v : V) (b : C) : ℝ :=
  maximumGap (rank v) rho / 2 + runningMin (rank v) rho b

theorem biasedVoterDistance_nonneg (rank : V → C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (v : V) (b : C) : 0 ≤ biasedVoterDistance rank rho v b := by
  exact add_nonneg (div_nonneg (maximumGap_nonneg _ _) (by norm_num))
    (runningMin_nonneg _ _ hrho _)

/-- The triangle inequality with the voter as an endpoint. -/
theorem biasedVoterDistance_le_add (rank : V → C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (v : V) (a b : C) :
    biasedVoterDistance rank rho v a ≤ biasedVoterDistance rank rho v b +
      biasedCandidateDistance rho a b := by
  classical
  by_cases hab : a = b
  · subst b
    simp
  · have h1 := runningMin_le_self (rank v) rho a
    have h2 := runningMin_nonneg (rank v) rho hrho b
    have h3 := le_max_left (rho a) (rho b)
    simp only [biasedCandidateDistance, if_neg hab, biasedVoterDistance]
    linarith

/-- The triangle inequality with the voter between the candidates. -/
theorem biasedCandidateDistance_le_voter_sum (rank : V → C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (v : V) (a b : C) :
    biasedCandidateDistance rho a b ≤
      biasedVoterDistance rank rho v a + biasedVoterDistance rank rho v b := by
  classical
  by_cases hab : a = b
  · subst b
    simp only [biasedCandidateDistance_self]
    exact add_nonneg (biasedVoterDistance_nonneg rank rho hrho v a)
      (biasedVoterDistance_nonneg rank rho hrho v a)
  · have h1 := le_maximumGap (rank v) rho a
    have h2 := le_maximumGap (rank v) rho b
    have ha := runningMin_nonneg (rank v) rho hrho a
    have hb := runningMin_nonneg (rank v) rho hrho b
    simp only [biasedCandidateDistance, if_neg hab, biasedVoterDistance]
    apply max_le <;> linarith

/-- Candidate and voter distance profiles in finite-dimensional sup space. -/
noncomputable def biasedEmbedding (rank : V → C → ℕ) (rho : C → ℝ) :
    V ⊕ C → (C → ℝ)
  | Sum.inl v => biasedVoterDistance rank rho v
  | Sum.inr c => biasedCandidateDistance rho c

/-- The actual pseudometric extension. Its voter-to-voter distances are the
sup distances between the prescribed candidate-distance profiles. -/
noncomputable abbrev biasedPseudoMetricSpace (rank : V → C → ℕ) (rho : C → ℝ) :
    PseudoMetricSpace (V ⊕ C) :=
  PseudoMetricSpace.induced (biasedEmbedding rank rho) inferInstance

theorem biased_dist_voter_candidate (rank : V → C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (v : V) (b : C) :
    letI := biasedPseudoMetricSpace rank rho
    dist (Sum.inl v) (Sum.inr b) = biasedVoterDistance rank rho v b := by
  change dist (biasedVoterDistance rank rho v) (biasedCandidateDistance rho b) = _
  exact dist_profile_eq (biasedCandidateDistance rho) (biasedVoterDistance rank rho v)
    (biasedCandidateDistance_self rho) (biasedCandidateDistance_comm rho)
    (biasedVoterDistance_nonneg rank rho hrho v)
    (biasedVoterDistance_le_add rank rho hrho v)
    (biasedCandidateDistance_le_voter_sum rank rho hrho v) b

theorem biased_dist_candidate_candidate (rank : V → C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (a b : C) :
    letI := biasedPseudoMetricSpace rank rho
    dist (Sum.inr a : V ⊕ C) (Sum.inr b) = biasedCandidateDistance rho a b := by
  change dist (biasedCandidateDistance rho a) (biasedCandidateDistance rho b) = _
  apply dist_profile_eq (biasedCandidateDistance rho) (biasedCandidateDistance rho a)
    (biasedCandidateDistance_self rho) (biasedCandidateDistance_comm rho)
    (biasedCandidateDistance_nonneg rho hrho a)
  · intro c d
    simpa only [biasedCandidateDistance_comm rho c d] using
      biasedCandidateDistance_triangle rho hrho a d c
  · intro c d
    simpa only [biasedCandidateDistance_comm rho c a] using
      biasedCandidateDistance_triangle rho hrho c a d

/-- The constructed distances are consistent with the given rankings. -/
theorem biased_metric_consistent (rank : V → C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (v : V) (b c : C) (hcb : rank v c ≤ rank v b) :
    letI := biasedPseudoMetricSpace rank rho
    dist (Sum.inl v) (Sum.inr b) ≤ dist (Sum.inl v) (Sum.inr c) := by
  rw [biased_dist_voter_candidate rank rho hrho,
    biased_dist_voter_candidate rank rho hrho]
  have h := runningMin_antitone_rank (rank v) rho b c hcb
  dsimp [biasedVoterDistance]
  linarith

/-- Every voter has the asserted distance from the reference candidate. -/
theorem biased_distance_to_reference (rank : V → C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (a : C) (ha : rho a = 0) (v : V) :
    letI := biasedPseudoMetricSpace rank rho
    dist (Sum.inl v) (Sum.inr a) = maximumGap (rank v) rho / 2 := by
  rw [biased_dist_voter_candidate rank rho hrho]
  simp only [biasedVoterDistance, runningMin_at_zero (rank v) rho hrho a ha, add_zero]

/-- The reference candidate minimizes each voter's distance separately. -/
theorem biased_reference_nearest (rank : V → C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (a : C) (ha : rho a = 0) (v : V) (b : C) :
    letI := biasedPseudoMetricSpace rank rho
    dist (Sum.inl v) (Sum.inr a) ≤ dist (Sum.inl v) (Sum.inr b) := by
  rw [biased_distance_to_reference rank rho hrho a ha,
    biased_dist_voter_candidate rank rho hrho]
  exact le_add_of_nonneg_right (runningMin_nonneg (rank v) rho hrho b)

/-- The social cost of the reference candidate is exactly half the mean gap. -/
theorem biased_reference_cost [Fintype V]
    (rank : V → C → ℕ) (rho : C → ℝ) (w : V → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (a : C) (ha : rho a = 0) :
    letI := biasedPseudoMetricSpace rank rho
    expectation w (fun v => dist (Sum.inl v) (Sum.inr a)) =
      expectation w (fun v => maximumGap (rank v) rho) / 2 := by
  simp_rw [biased_distance_to_reference rank rho hrho a ha]
  unfold expectation
  simp_rw [← mul_div_assoc]
  rw [Finset.sum_div]

/-- Exact lottery social cost for the constructed pseudometric. -/
theorem biased_lottery_cost [Fintype V]
    (rank : V → C → ℕ) (rho : C → ℝ) (w : V → ℝ) (D : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (hDsum : ∑ c, D c = 1) :
    letI := biasedPseudoMetricSpace rank rho
    expectation w (fun v => expectation D (fun b => dist (Sum.inl v) (Sum.inr b))) =
      expectation w (fun v => maximumGap (rank v) rho) / 2 +
        expectation w (fun v => expectation D (runningMin (rank v) rho)) := by
  simp_rw [biased_dist_voter_candidate rank rho hrho, biasedVoterDistance,
    expectation_add, expectation_const hDsum]
  congr 1
  unfold expectation
  simp_rw [← mul_div_assoc]
  rw [Finset.sum_div]

/-- In particular the reference candidate minimizes social cost. -/
theorem biased_reference_cost_minimal [Fintype V]
    (rank : V → C → ℕ) (rho : C → ℝ) (w : V → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (hw : ∀ v, 0 ≤ w v) (a : C) (ha : rho a = 0) (b : C) :
    letI := biasedPseudoMetricSpace rank rho
    expectation w (fun v => dist (Sum.inl v) (Sum.inr a)) ≤
      expectation w (fun v => dist (Sum.inl v) (Sum.inr b)) := by
  exact expectation_mono hw (fun v => biased_reference_nearest rank rho hrho a ha v b)

/-- Every strict violation of (2.1) is a strict social-cost violation in the
actual constructed pseudometric. Positivity of the denominator is handled
separately by the shifted construction below. -/
theorem biased_cost_strict_violation [Fintype V]
    (rank : V → C → ℕ) (rho : C → ℝ) (w : V → ℝ) (D : C → ℝ) (lam : ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (hDsum : ∑ c, D c = 1)
    (a : C) (ha : rho a = 0)
    (hviolation : lam * expectation w (fun v => maximumGap (rank v) rho) <
      expectation w (fun v => expectation D (runningMin (rank v) rho))) :
    letI := biasedPseudoMetricSpace rank rho
    (1 + 2 * lam) * expectation w (fun v => dist (Sum.inl v) (Sum.inr a)) <
      expectation w (fun v => expectation D (fun b => dist (Sum.inl v) (Sum.inr b))) := by
  rw [biased_reference_cost rank rho w hrho a ha,
    biased_lottery_cost rank rho w D hrho hDsum]
  linarith

/-- Adding a positive constant to every distance between distinct points turns
any pseudometric into a genuine metric. -/
noncomputable abbrev separatedMetricSpace {X : Type*}
    (m : PseudoMetricSpace X) (eps : ℝ) (heps : 0 < eps) : MetricSpace X := by
  classical
  letI := m
  exact {
    dist := fun x y => if x = y then 0 else dist x y + eps
    dist_self := by intro x; simp
    dist_comm := by intro x y; simp only [eq_comm, dist_comm]
    dist_triangle := by
      intro x y z
      by_cases hxy : x = y
      · subst y
        simp
      by_cases hyz : y = z
      · subst z
        simp
      by_cases hxz : x = z
      · subst z
        simp only [ite_true, if_neg hxy, if_neg (Ne.symm hxy)]
        have h1 : 0 ≤ dist x y := dist_nonneg
        have h2 : 0 ≤ dist y x := dist_nonneg
        linarith
      · simp only [if_neg hxy, if_neg hyz, if_neg hxz]
        have h := dist_triangle x y z
        linarith
    eq_of_dist_eq_zero := by
      intro x y h
      by_contra hxy
      rw [if_neg hxy] at h
      have hn : 0 ≤ dist x y := dist_nonneg
      linarith
  }

theorem separated_dist_of_ne {X : Type*} (m : PseudoMetricSpace X)
    (eps : ℝ) (heps : 0 < eps) (x y : X) (hxy : x ≠ y) :
    letI : PseudoMetricSpace X := (separatedMetricSpace m eps heps).toPseudoMetricSpace
    dist x y = @dist X m.toDist x y + eps := by
  classical
  change (if x = y then 0 else @dist X m.toDist x y + eps) = _
  exact if_neg hxy

/-- The positive-distance version used to witness a distortion ratio. -/
noncomputable abbrev regularizedBiasedMetricSpace
    (rank : V → C → ℕ) (rho : C → ℝ) (eps : ℝ) (heps : 0 < eps) :
    MetricSpace (V ⊕ C) :=
  separatedMetricSpace (biasedPseudoMetricSpace rank rho) eps heps

theorem regularized_dist_voter_candidate
    (rank : V → C → ℕ) (rho : C → ℝ) (hrho : ∀ c, 0 ≤ rho c)
    (eps : ℝ) (heps : 0 < eps) (v : V) (b : C) :
    letI : PseudoMetricSpace (V ⊕ C) :=
      (regularizedBiasedMetricSpace rank rho eps heps).toPseudoMetricSpace
    dist (Sum.inl v) (Sum.inr b) = biasedVoterDistance rank rho v b + eps := by
  calc
    _ = @dist (V ⊕ C) (biasedPseudoMetricSpace rank rho).toDist
        (Sum.inl v) (Sum.inr b) + eps :=
      separated_dist_of_ne (biasedPseudoMetricSpace rank rho) eps heps
        (Sum.inl v) (Sum.inr b) (by simp)
    _ = _ := congrArg (fun r : ℝ => r + eps) (biased_dist_voter_candidate rank rho hrho v b)

theorem regularized_metric_consistent
    (rank : V → C → ℕ) (rho : C → ℝ) (hrho : ∀ c, 0 ≤ rho c)
    (eps : ℝ) (heps : 0 < eps) (v : V) (b c : C) (hcb : rank v c ≤ rank v b) :
    letI : PseudoMetricSpace (V ⊕ C) :=
      (regularizedBiasedMetricSpace rank rho eps heps).toPseudoMetricSpace
    dist (Sum.inl v) (Sum.inr b) ≤ dist (Sum.inl v) (Sum.inr c) := by
  rw [regularized_dist_voter_candidate rank rho hrho,
    regularized_dist_voter_candidate rank rho hrho]
  have h := runningMin_antitone_rank (rank v) rho b c hcb
  dsimp [biasedVoterDistance]
  linarith

/-- Regularization adds exactly eps to the reference social cost. -/
theorem regularized_reference_cost [Fintype V]
    (rank : V → C → ℕ) (rho : C → ℝ) (w : V → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (hwsum : ∑ v, w v = 1)
    (a : C) (ha : rho a = 0) (eps : ℝ) (heps : 0 < eps) :
    letI : PseudoMetricSpace (V ⊕ C) :=
      (regularizedBiasedMetricSpace rank rho eps heps).toPseudoMetricSpace
    expectation w (fun v => dist (Sum.inl v) (Sum.inr a)) =
      expectation w (fun v => maximumGap (rank v) rho) / 2 + eps := by
  simp_rw [regularized_dist_voter_candidate rank rho hrho, biasedVoterDistance,
    runningMin_at_zero _ rho hrho a ha, add_zero]
  rw [expectation_add, expectation_const hwsum]
  congr 1
  unfold expectation
  simp_rw [← mul_div_assoc]
  rw [Finset.sum_div]

/-- Regularization adds exactly eps to the lottery social cost as well. -/
theorem regularized_lottery_cost [Fintype V]
    (rank : V → C → ℕ) (rho : C → ℝ) (w : V → ℝ) (D : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (hwsum : ∑ v, w v = 1) (hDsum : ∑ c, D c = 1)
    (eps : ℝ) (heps : 0 < eps) :
    letI : PseudoMetricSpace (V ⊕ C) :=
      (regularizedBiasedMetricSpace rank rho eps heps).toPseudoMetricSpace
    expectation w (fun v => expectation D (fun b => dist (Sum.inl v) (Sum.inr b))) =
      expectation w (fun v => maximumGap (rank v) rho) / 2 +
        expectation w (fun v => expectation D (runningMin (rank v) rho)) + eps := by
  simp_rw [regularized_dist_voter_candidate rank rho hrho, biasedVoterDistance,
    expectation_add, expectation_const hDsum, expectation_const hwsum]
  congr 2
  unfold expectation
  simp_rw [← mul_div_assoc]
  rw [Finset.sum_div]

/-- The reference candidate stays optimal under regularization. -/
theorem regularized_reference_cost_minimal [Fintype V]
    (rank : V → C → ℕ) (rho : C → ℝ) (w : V → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (hw : ∀ v, 0 ≤ w v) (a : C) (ha : rho a = 0)
    (eps : ℝ) (heps : 0 < eps) (b : C) :
    letI : PseudoMetricSpace (V ⊕ C) :=
      (regularizedBiasedMetricSpace rank rho eps heps).toPseudoMetricSpace
    expectation w (fun v => dist (Sum.inl v) (Sum.inr a)) ≤
      expectation w (fun v => dist (Sum.inl v) (Sum.inr b)) := by
  apply expectation_mono hw
  intro v
  rw [regularized_dist_voter_candidate rank rho hrho,
    regularized_dist_voter_candidate rank rho hrho]
  dsimp [biasedVoterDistance]
  rw [runningMin_at_zero _ rho hrho a ha]
  have h := runningMin_nonneg (rank v) rho hrho b
  linarith

/-- Full reverse witness for Lemma 2.4. Every strict violation of the
running-minimum inequality yields a finite genuine metric, consistent with the
rankings, with positive optimal social cost and distortion strictly above the
claimed bound. This includes mean gap zero and uses no limiting argument. -/
theorem exists_metric_of_strict_runningMin_violation [Fintype V]
    (rank : V → C → ℕ) (rho : C → ℝ) (w : V → ℝ) (D : C → ℝ) (lam : ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (hw : ∀ v, 0 ≤ w v)
    (hwsum : ∑ v, w v = 1) (hDsum : ∑ c, D c = 1) (hlam : 0 ≤ lam)
    (a : C) (ha : rho a = 0)
    (hviolation : lam * expectation w (fun v => maximumGap (rank v) rho) <
      expectation w (fun v => expectation D (runningMin (rank v) rho))) :
    ∃ m : MetricSpace (V ⊕ C), letI : PseudoMetricSpace (V ⊕ C) := m.toPseudoMetricSpace
      (∀ (v : V) (b c : C), rank v c ≤ rank v b →
        dist (Sum.inl v) (Sum.inr b) ≤ dist (Sum.inl v) (Sum.inr c)) ∧
      (∀ b : C, expectation w (fun v => dist (Sum.inl v) (Sum.inr a)) ≤
        expectation w (fun v => dist (Sum.inl v) (Sum.inr b))) ∧
      0 < expectation w (fun v => dist (Sum.inl v) (Sum.inr a)) ∧
      1 + 2 * lam <
        expectation w (fun v => expectation D (fun b => dist (Sum.inl v) (Sum.inr b))) /
          expectation w (fun v => dist (Sum.inl v) (Sum.inr a)) := by
  let G := expectation w (fun v => maximumGap (rank v) rho)
  let N := expectation w (fun v => expectation D (runningMin (rank v) rho))
  let gap := N - lam * G
  have hgap : 0 < gap := sub_pos.mpr hviolation
  let eps := gap / (4 * lam + 2)
  have hden : 0 < 4 * lam + 2 := by linarith
  have heps : 0 < eps := div_pos hgap hden
  have hepsEq : eps * (4 * lam + 2) = gap := div_mul_cancel₀ _ (ne_of_gt hden)
  have hG : 0 ≤ G := by
    apply Finset.sum_nonneg
    intro v _
    exact mul_nonneg (hw v) (maximumGap_nonneg (rank v) rho)
  have hbase : 0 < G / 2 + eps := by linarith
  have hprod : 0 ≤ lam * eps := mul_nonneg hlam (le_of_lt heps)
  have hexcess : (1 + 2 * lam) * (G / 2 + eps) < G / 2 + N + eps := by
    dsimp [gap] at hepsEq
    nlinarith
  refine ⟨regularizedBiasedMetricSpace rank rho eps heps, ?_⟩
  refine ⟨fun v b c h => regularized_metric_consistent rank rho hrho eps heps v b c h,
    fun b => regularized_reference_cost_minimal rank rho w hrho hw a ha eps heps b, ?_, ?_⟩
  · rw [regularized_reference_cost rank rho w hrho hwsum a ha]
    exact hbase
  · rw [regularized_reference_cost rank rho w hrho hwsum a ha,
      regularized_lottery_cost rank rho w D hrho hwsum hDsum]
    exact (lt_div_iff₀ hbase).mpr hexcess

end Construction

end OptimalG
