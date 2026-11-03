import OptimalG.UniversalMovingBound
import OptimalG.UniversalBasicRows

/-! Sparse LP rows interpreted using actual integral averages. -/
namespace OptimalG.UniversalLP
open Set

/-- The encoded binary-integral row follows from integrating actual Election 2. -/
theorem binary_integral_row {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass (L : ℝ) phi)
    {i j : ℕ} (hi0 : 0 < i) (hi1 : i < 200) (hji : j + 1 ≤ i) (hjL : node (j + 1) ≤ L) :
    RowHolds (.binaryIntegral i j) (gridValues phi) := by
  have hj1 : j + 1 ≤ 200 := hji.trans hi1.le
  have hk1 : 200 - i + j + 1 ≤ 200 := by omega
  have hiR : (i : ℝ) < 200 := by exact_mod_cast hi1
  have hiR0 : (0 : ℝ) < i := by exact_mod_cast hi0
  have hp : (i : ℝ) / 200 ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by linarith⟩
  have hab : (j : ℝ) / 200 < ((j + 1 : ℕ) : ℝ) / 200 := by push_cast; linarith
  have hqp : ((j + 1 : ℕ) : ℝ) / 200 ≤ (i : ℝ) / 200 :=
    div_le_div_of_nonneg_right (by exact_mod_cast hji) (by norm_num)
  have hqL : ((j + 1 : ℕ) : ℝ) / 200 ≤ (L : ℝ) := by
    have hh : (node (j + 1) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hjL
    simpa only [node_cast] using hh
  have hh := h.two_class_bin_integral (by norm_num [L]) (by norm_num [L]) hp
    (show 0 ≤ (j : ℝ) / 200 by positivity) hab hqp hqL
  have hindex : ((200 - i + j : ℕ) : ℝ) / 200 = 1 - (i : ℝ) / 200 + (j : ℝ) / 200 := by
    rw [Nat.cast_add, Nat.cast_sub hi1.le]
    push_cast
    ring
  have hindex1 : ((200 - i + j + 1 : ℕ) : ℝ) / 200 = 1 - (i : ℝ) / 200 + ((j + 1 : ℕ) : ℝ) / 200 := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hi1.le]
    push_cast
    ring
  rw [rowHolds_iff_terms]
  simp only [rowTerms, termsValue, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
  rw [show 201 + j + 1 = 201 + (j + 1) by omega,
    termValue_V phi (200 - i + j + 1) _ hk1,
    termValue_V phi (200 - i + j) _ (by omega),
    termValue_V phi (j + 1) _ hj1, termValue_V phi j _ (by omega),
    termValue_J phi i _ hi1.le]
  simp only [rowRhs, Rat.cast_zero, Rat.cast_neg, Rat.cast_mul, Rat.cast_sub,
    Rat.cast_div, Rat.cast_add, Rat.cast_natCast, node_cast, hindex, hindex1]
  have hwidth : ((j + 1 : ℕ) : ℝ) / 200 - (j : ℝ) / 200 = 1 / 200 := by push_cast; ring
  rw [hwidth] at hh
  push_cast at hh ⊢
  nlinarith

/-- Every sparse moving row is an actual necessary inequality once the two
certified ratio lower bounds are supplied. -/
theorem moving_row {phi : ℝ → ℝ} (h : NormalizedNecessaryConditions (L : ℝ) phi)
    {pi i j k l z0 z1 : ℕ} {x y : ℚ}
    (hpi0 : 0 < pi) (hpi1 : pi < 200)
    (hij : i < j) (hkl : k < l) (hzz : z0 < z1) (hz1 : z1 ≤ 200)
    (hjL : node j < L) (hjp : j < pi)
    (hpk : 1 - node pi ≤ node k) (hlL : node l < L)
    (hzL : L + (1 - node pi) / 2 < node z0)
    (hkap : 0 ≤ 1 - node pi + node k - L)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxX : (x : ℝ) ≤ activationPrimitive phi (1 - (1 - (node pi : ℝ))) /
      activationPrimitive phi (1 - (node pi : ℝ)))
    (hyY : (y : ℝ) ≤ binAverage
      (fun z => activationPrimitive phi (z - (1 - (node pi : ℝ))) - activationPrimitive phi z)
      (node z0 : ℝ) (node z1 : ℝ) / activationPrimitive phi (1 - (node pi : ℝ))) :
    RowHolds (.moving pi i j k l z0 z1 x y) (gridValues phi) := by
  have hpi : (node pi : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    simp only [node_cast]
    constructor
    · exact div_pos (by exact_mod_cast hpi0) (by norm_num)
    · have hh : (pi : ℝ) < 200 := by exact_mod_cast hpi1
      linarith
  have hp : 1 - (node pi : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hpi.2], by linarith [hpi.1]⟩
  have hL1 : (L : ℝ) < 1 := by norm_num [L]
  have ha : (node i : ℝ) < (node j : ℝ) := by simp only [node_cast]; exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by norm_num)
  have hb : (node k : ℝ) < (node l : ℝ) := by simp only [node_cast]; exact div_lt_div_of_pos_right (by exact_mod_cast hkl) (by norm_num)
  have hz : (node z0 : ℝ) < (node z1 : ℝ) := by simp only [node_cast]; exact div_lt_div_of_pos_right (by exact_mod_cast hzz) (by norm_num)
  have haL : (node j : ℝ) < (L : ℝ) := by exact_mod_cast hjL
  have hap : (node j : ℝ) < 1 - (1 - (node pi : ℝ)) := by
    simp only [sub_sub_cancel, node_cast]
    exact div_lt_div_of_pos_right (by exact_mod_cast hjp) (by norm_num)
  have hpb : 1 - (node pi : ℝ) ≤ (node k : ℝ) := by exact_mod_cast hpk
  have hbL : (node l : ℝ) < (L : ℝ) := by exact_mod_cast hlL
  have hzmin : (L : ℝ) + (1 - (node pi : ℝ)) / 2 < (node z0 : ℝ) := by exact_mod_cast hzL
  have hk : 0 ≤ 1 - (node pi : ℝ) + (node k : ℝ) - (L : ℝ) := by exact_mod_cast hkap
  have hzmax : (node z1 : ℝ) ≤ 1 := by simpa only [node_cast] using (grid_rank_mem hz1).2
  have hj200 : j ≤ 200 := by omega
  have hi200 : i ≤ 200 := by omega
  have hl200 : l ≤ 200 := by
    have hh : (l : ℝ) / 200 < 1 := by simpa only [node_cast] using hbL.trans hL1
    have hh' : (l : ℝ) < 200 := by linarith
    have hh'' : l < 200 := by exact_mod_cast hh'
    omega
  have hk200 : k ≤ 200 := by omega
  have hz0200 : z0 ≤ 200 := by omega
  have hh := h.moving_bin_row (by norm_num [L]) hL1 hp
    (show 0 ≤ (node i : ℝ) by simp only [node_cast]; positivity) ha haL hap hpb hb hbL hzmin hz hzmax hk
    (by exact_mod_cast hx) (by exact_mod_cast hy) hxX hyY
  rw [h.toNormalizedNecessaryTwoClass.activation_binAverage (by simp only [node_cast]; positivity) ha (haL.le.trans hL1.le),
    h.toNormalizedNecessaryTwoClass.activation_binAverage (by simp only [node_cast]; positivity) hb (hbL.le.trans hL1.le),
    h.toNormalizedNecessaryTwoClass.activation_binAverage (by simp only [node_cast]; positivity) hz hzmax] at hh
  rw [rowHolds_iff_terms]
  simp only [rowTerms, termsValue, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
  rw [termValue_J phi j _ hj200, termValue_J phi i _ hi200,
    termValue_J phi l _ hl200, termValue_J phi k _ hk200,
    termValue_J phi z1 _ hz1, termValue_J phi z0 _ hz0200]
  simp only [rowRhs, Rat.cast_zero, Rat.cast_neg, Rat.cast_mul, Rat.cast_sub, Rat.cast_add,
    Rat.cast_div, Rat.cast_natCast, node_cast]
  simp only [node_cast, ← sub_div, div_div_eq_mul_div] at hh
  convert! hh using 1
  ring

end OptimalG.UniversalLP
