import OptimalG.RankIntegral
import OptimalG.BiasedMetric
import OptimalG.Telescoping

/-!
# Threshold slices of finite rank lines

These definitions include candidates of probability zero. The first missing
candidate controls the initial slice, even when its own rank interval has zero width.
-/

namespace OptimalG

open Set MeasureTheory
open scoped BigOperators Interval

section Prefix

variable {n : ℕ} [Nonempty (Fin n)]

/-- Index of the first candidate outside `S`, or `n` if every candidate is in `S`. -/
noncomputable def prefixBoundary (S : Finset (Fin n)) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => if i ∈ S then n else i.val)

theorem before_prefixBoundary_iff (S : Finset (Fin n)) (i : Fin n) :
    i.val < prefixBoundary S ↔ ∀ j : Fin n, j.val ≤ i.val → j ∈ S := by
  classical
  simp only [prefixBoundary, Finset.lt_inf'_iff, Finset.mem_univ, forall_true_left]
  constructor
  · intro h j hji
    by_contra hj
    have hh := h j
    simp only [if_neg hj] at hh
    omega
  · intro h j
    by_cases hj : j ∈ S
    · simpa only [if_pos hj] using i.isLt
    · simp only [if_neg hj]
      by_contra hle
      exact hj (h j (by omega))

theorem prefixBoundary_le_outside (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    prefixBoundary S ≤ i.val := by
  classical
  have h := Finset.inf'_le (fun j : Fin n => if j ∈ S then n else j.val)
    (Finset.mem_univ i)
  simpa [prefixBoundary, hi] using h

theorem prefixBoundary_le (S : Finset (Fin n)) : prefixBoundary S ≤ n := by
  classical
  let i : Fin n := Classical.arbitrary _
  have h := Finset.inf'_le (fun j : Fin n => if j ∈ S then n else j.val)
    (Finset.mem_univ i)
  change prefixBoundary S ≤ (if i ∈ S then n else i.val) at h
  split_ifs at h with hi
  · exact h
  · exact le_trans h i.isLt.le

theorem prefixCut_le_mass (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i) (S : Finset (Fin n)) :
    rankCut D (prefixBoundary S) ≤ ∑ i ∈ S, D i := by
  classical
  unfold rankCut
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact (before_prefixBoundary_iff S i).mp (Finset.mem_filter.mp hi).2 i le_rfl
  · intro i _ _
    exact hD i

theorem runningMin_gt_iff (rho : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    t < runningMin (fun j : Fin n => j.val) rho i ↔
      ∀ j : Fin n, j.val ≤ i.val → t < rho j := by
  simp only [runningMin, Finset.lt_inf'_iff, Finset.mem_univ, forall_true_left]
  constructor
  · intro h j hji
    simpa only [if_pos hji] using h j
  · intro h j
    split_ifs with hji
    · exact h j hji
    · exact h i le_rfl

noncomputable def thresholdSet (rho : Fin n → ℝ) (t : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => t < rho i)

noncomputable def thresholdWidth (D rho : Fin n → ℝ) (t : ℝ) : ℝ :=
  rankCut D (prefixBoundary (thresholdSet rho t))

/-- The slice width is the lottery mass whose running minimum exceeds the threshold. -/
theorem thresholdWidth_eq_sum (D rho : Fin n → ℝ) (t : ℝ) :
    thresholdWidth D rho t = ∑ i,
      if t < runningMin (fun j : Fin n => j.val) rho i then D i else 0 := by
  classical
  unfold thresholdWidth rankCut
  apply Finset.sum_congr rfl
  intro i _
  have heq : i.val < prefixBoundary (thresholdSet rho t) ↔
      t < runningMin (fun j : Fin n => j.val) rho i := by
    rw [before_prefixBoundary_iff, runningMin_gt_iff]
    simp [thresholdSet]
  simp only [heq]

theorem thresholdWidth_nonneg (D rho : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i) (t : ℝ) :
    0 ≤ thresholdWidth D rho t := by
  rw [thresholdWidth_eq_sum]
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hD i
  · rfl

theorem thresholdWidth_le_mass (D rho : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i) (t : ℝ) :
    thresholdWidth D rho t ≤ ∑ i ∈ thresholdSet rho t, D i := by
  classical
  rw [thresholdWidth_eq_sum, ← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    have hrun := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_of_lt_of_le hrun (runningMin_le_self _ rho i)⟩
  · intro i _ _
    exact hD i

theorem thresholdWidth_le_referenceRank (D rho : Fin n → ℝ)
    (hD : ∀ i, 0 ≤ D i) (a : Fin n) (ha : rho a = 0) (t : ℝ) (ht : 0 ≤ t) :
    thresholdWidth D rho t ≤ rankCut D a.val := by
  apply rankCut_mono D hD
  apply prefixBoundary_le_outside
  simp [thresholdSet, ha, not_lt.mpr ht]

/-- One past the last ordinal position in a candidate set; zero for the empty set. -/
def lastIndex (S : Finset (Fin n)) : ℕ := S.sup (fun i => i.val + 1)

omit [Nonempty (Fin n)] in
theorem lastIndex_le (S : Finset (Fin n)) : lastIndex S ≤ n := by
  apply Finset.sup_le
  intro i _
  exact i.isLt

omit [Nonempty (Fin n)] in
theorem member_lt_lastIndex (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    i.val < lastIndex S := by
  exact Finset.le_sup (f := fun j : Fin n => j.val + 1) hi

omit [Nonempty (Fin n)] in
theorem mass_le_lastCut (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i) (S : Finset (Fin n)) :
    (∑ i ∈ S, D i) ≤ rankCut D (lastIndex S) := by
  classical
  calc
    (∑ i ∈ S, D i) = ∑ i ∈ S, if i.val < lastIndex S then D i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [member_lt_lastIndex S i hi]
    _ ≤ ∑ i : Fin n, if i.val < lastIndex S then D i else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      split_ifs
      · exact hD i
      · rfl
    _ = rankCut D (lastIndex S) := rfl

noncomputable def thresholdRight (D rho : Fin n → ℝ) (t : ℝ) : ℝ :=
  rankCut D (lastIndex (thresholdSet rho t))

/-- Every candidate above threshold t+Δ precedes every candidate at or below t. -/
theorem threshold_candidates_separated (rho : Fin n → ℝ) (t : ℝ)
    (b c : Fin n) (hb : t + maximumGap (fun i : Fin n => i.val) rho < rho b)
    (hc : rho c ≤ t) : b.val < c.val := by
  by_contra hbc
  have hmin := runningMin_le_of_rank_le (fun i : Fin n => i.val) rho b c (by omega)
  have hgap := le_maximumGap (fun i : Fin n => i.val) rho b
  linarith

/-- The separation in (5.1), proved from the actual running maximum gap. -/
theorem threshold_separation (D rho : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i) (t : ℝ) :
    thresholdRight D rho (t + maximumGap (fun i : Fin n => i.val) rho) ≤
      thresholdWidth D rho t := by
  classical
  apply rankCut_mono D hD
  apply Finset.sup_le
  intro b hb
  apply Nat.succ_le_of_lt
  rw [before_prefixBoundary_iff]
  intro c hcb
  by_contra hc
  have hb' : t + maximumGap (fun i : Fin n => i.val) rho < rho b := by
    simpa [thresholdSet] using hb
  have hc' : rho c ≤ t := by simpa [thresholdSet] using hc
  have hbc := threshold_candidates_separated rho t b c hb' hc'
  omega

theorem thresholdWidth_zero_above (D rho : Fin n → ℝ) (X t : ℝ)
    (hX : ∀ i, rho i ≤ X) (ht : X ≤ t) : thresholdWidth D rho t = 0 := by
  classical
  rw [thresholdWidth_eq_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hbound := le_trans (runningMin_le_self (fun j : Fin n => j.val) rho i)
    (le_trans (hX i) ht)
  simp [not_lt.mpr hbound]

end Prefix

/-- The elementary real-valued layer-cake integral for one height. -/
theorem integral_below_height (h X : ℝ) (hh : 0 ≤ h) (hX : h ≤ X) :
    IntervalIntegrable (fun t : ℝ => if t < h then (1 : ℝ) else 0) volume 0 X ∧
      (∫ t in (0 : ℝ)..X, if t < h then (1 : ℝ) else 0) = h := by
  let f : ℝ → ℝ := fun t => if t < h then 1 else 0
  have hleft : IntervalIntegrable f volume 0 h := by
    apply (intervalIntegrable_const (c := (1 : ℝ))).congr_uIoo
    rw [uIoo_of_le hh]
    intro t ht
    simp [f, ht.2]
  have hright : IntervalIntegrable f volume h X := by
    apply (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo
    rw [uIoo_of_le hX]
    intro t ht
    simp [f, not_lt.mpr ht.1.le]
  refine ⟨hleft.trans hright, ?_⟩
  change (∫ t in (0 : ℝ)..X, f t) = h
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  have hl : (∫ t in (0 : ℝ)..h, f t) = h := by
    calc
      _ = ∫ _t in (0 : ℝ)..h, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hh
        intro t ht
        simp [f, ht.2]
      _ = h := by simp
  have hr : (∫ t in h..X, f t) = 0 := by
    calc
      _ = ∫ _t in h..X, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hX
        intro t ht
        simp [f, not_lt.mpr ht.1.le]
      _ = 0 := by simp
  rw [hl, hr, add_zero]

/-- Finite layer cake: the integral of the threshold slice is its running-minimum cost. -/
theorem threshold_layer_cake {n : ℕ} [Nonempty (Fin n)]
    (D rho : Fin n → ℝ) (X : ℝ) (hrho : ∀ i, 0 ≤ rho i)
    (hX : ∀ i, rho i ≤ X) :
    IntervalIntegrable (thresholdWidth D rho) volume 0 X ∧
      (∫ t in (0 : ℝ)..X, thresholdWidth D rho t) =
        expectation D (runningMin (fun j : Fin n => j.val) rho) := by
  classical
  let heights := runningMin (fun j : Fin n => j.val) rho
  let f : Fin n → ℝ → ℝ := fun i t => if t < heights i then 1 else 0
  have hf : ∀ i, IntervalIntegrable (f i) volume 0 X := by
    intro i
    exact (integral_below_height (heights i) X
      (runningMin_nonneg _ rho hrho i)
      (le_trans (runningMin_le_self _ rho i) (hX i))).1
  have heq : thresholdWidth D rho = fun t => expectation D (fun i => f i t) := by
    funext t
    rw [thresholdWidth_eq_sum]
    unfold expectation
    apply Finset.sum_congr rfl
    intro i _
    simp only [f, heights]
    split_ifs <;> simp
  rw [heq]
  constructor
  · have heqsum : (fun t => expectation D (fun i => f i t)) =
        ∑ i, fun t => D i * f i t := by
      funext t
      simp [expectation]
    rw [heqsum]
    exact IntervalIntegrable.sum _ (fun i _ => (hf i).const_mul (D i))
  · rw [integral_expectation D f 0 X hf]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (integral_below_height (heights i) X
      (runningMin_nonneg _ rho hrho i)
      (le_trans (runningMin_le_self _ rho i) (hX i))).2

end OptimalG
