import OptimalG.UniversalLPBox

/-! The slope and moment LP rows follow from the actual derivative ceiling. -/
namespace OptimalG.UniversalLP
open Set

theorem termValue_J (phi : ℝ → ℝ) (i : ℕ) (q : ℚ) (hi : i ≤ 200) :
    termValue (gridValues phi) (i, q) = (q : ℝ) * activationPrimitive phi ((i : ℝ) / 200) := by
  have hi' : i < 402 := by omega
  simp [termValue, hi', gridValues, hi]

theorem termValue_V (phi : ℝ → ℝ) (i : ℕ) (q : ℚ) (hi : i ≤ 200) :
    termValue (gridValues phi) (201 + i, q) = (q : ℝ) * primitiveMoment phi ((i : ℝ) / 200) := by
  have hi' : 201 + i < 402 := by omega
  have hni : ¬201 + i ≤ 200 := by omega
  simp [termValue, hi', gridValues, hni]

theorem slope_row {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass (L : ℝ) phi)
    {i : ℕ} (hi : i < 200) : RowHolds (.slope i) (gridValues phi) := by
  have hi0 := grid_rank_mem hi.le
  have hi1 := grid_rank_mem (show i + 1 ≤ 200 by omega)
  have hiR : (i : ℝ) / 200 ≤ ((i + 1 : ℕ) : ℝ) / 200 := by push_cast; linarith
  have hh := h.primitive_increment_ceiling hi0.1 hiR hi1.2
  rw [rowHolds_iff_terms]
  simp only [rowTerms, termsValue, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
  rw [termValue_J phi (i + 1) 200 (by omega), termValue_J phi i (-200) hi.le]
  simp only [rowRhs]
  push_cast at hh ⊢
  nlinarith

theorem moment_up_row {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass (L : ℝ) phi)
    {i : ℕ} (hi : i < 200) : RowHolds (.momentUp i) (gridValues phi) := by
  have hi0 := grid_rank_mem hi.le
  have hi1 := grid_rank_mem (show i + 1 ≤ 200 by omega)
  have hiR : (i : ℝ) / 200 ≤ ((i + 1 : ℕ) : ℝ) / 200 := by push_cast; linarith
  have hh := h.moment_bin_upper hi0.1 hiR hi1.2
  rw [rowHolds_iff_terms]
  simp only [rowTerms, termsValue, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
  rw [show 201 + i + 1 = 201 + (i + 1) by omega,
    termValue_V phi (i + 1) 200 (by omega), termValue_V phi i (-200) hi.le,
    termValue_J phi i (-1) hi.le]
  simp only [rowRhs]
  unfold linePrimitive lineMoment at hh
  push_cast at hh ⊢
  simp only [node_cast]
  nlinarith

theorem moment_low_row {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass (L : ℝ) phi)
    {i : ℕ} (hi : i < 200) : RowHolds (.momentLow i) (gridValues phi) := by
  have hi0 := grid_rank_mem hi.le
  have hi1 := grid_rank_mem (show i + 1 ≤ 200 by omega)
  have hiR : (i : ℝ) / 200 ≤ ((i + 1 : ℕ) : ℝ) / 200 := by push_cast; linarith
  have hh := h.moment_bin_lower hi0.1 hiR hi1.2
  rw [rowHolds_iff_terms]
  simp only [rowTerms, termsValue, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
  rw [show 201 + i + 1 = 201 + (i + 1) by omega,
    termValue_V phi (i + 1) (-200) (by omega), termValue_V phi i 200 hi.le,
    termValue_J phi (i + 1) 1 (by omega)]
  simp only [rowRhs]
  unfold linePrimitive lineMoment at hh
  push_cast at hh ⊢
  simp only [node_cast]
  nlinarith

theorem binary_row {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass (L : ℝ) phi)
    {i j : ℕ} (hi0 : 0 < i) (hi1 : i < 200) (hji : j ≤ i) (hjL : node j ≤ L) :
    RowHolds (.binary i j) (gridValues phi) := by
  have hj1 : j ≤ 200 := hji.trans hi1.le
  have hk1 : 200 - i + j ≤ 200 := by omega
  have hiR : (i : ℝ) < 200 := by exact_mod_cast hi1
  have hiR0 : (0 : ℝ) < i := by exact_mod_cast hi0
  have hp : (i : ℝ) / 200 ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by linarith⟩
  have hqp : (j : ℝ) / 200 ≤ (i : ℝ) / 200 := by exact div_le_div_of_nonneg_right (by exact_mod_cast hji) (by norm_num)
  have hqL : (j : ℝ) / 200 ≤ (L : ℝ) := by
    have hh : (node j : ℝ) ≤ (L : ℝ) := by exact_mod_cast hjL
    simpa only [node_cast] using hh
  have hh := h.two_class_all (by norm_num [L]) (by norm_num [L])
    ((i : ℝ) / 200) ((j : ℝ) / 200) hp (by positivity) hqp hqL
  have hindex : ((200 - i + j : ℕ) : ℝ) / 200 = 1 - (i : ℝ) / 200 + (j : ℝ) / 200 := by
    rw [Nat.cast_add, Nat.cast_sub hi1.le]
    push_cast
    ring
  rw [rowHolds_iff_terms]
  simp only [rowTerms, termsValue, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
  rw [termValue_J phi (200 - i + j) (node i) hk1,
    termValue_J phi j (-node i) hj1,
    termValue_J phi i (-(L - node j)) hi1.le]
  simp only [rowRhs, Rat.cast_zero, Rat.cast_neg, Rat.cast_sub, node_cast, hindex]
  linarith

end OptimalG.UniversalLP
