import OptimalG.UniversalLPValue
import OptimalG.UniversalMomentBounds

/-! The rational LP box contains the actual primitive and integral moments. -/
namespace OptimalG.UniversalLP
open Set

noncomputable def gridValues (phi : ℝ → ℝ) (j : Variables) : ℝ :=
  if j.val ≤ 200 then activationPrimitive phi ((j.val : ℝ) / 200)
  else primitiveMoment phi (((j.val - 201 : ℕ) : ℝ) / 200)

theorem node_cast (i : ℕ) : ((node i : ℚ) : ℝ) = (i : ℝ) / 200 := by simp [node]
theorem Q_cast (r : ℚ) : ((Q r : ℚ) : ℝ) = linePrimitive (L : ℝ) r := by
  simp [Q, linePrimitive]
theorem VQ_cast (r : ℚ) : ((VQ r : ℚ) : ℝ) = lineMoment (L : ℝ) r := by
  simp [VQ, lineMoment]

theorem grid_rank_mem {i : ℕ} (hi : i ≤ 200) : (i : ℝ) / 200 ∈ Icc (0 : ℝ) 1 := by
  have hh : (i : ℝ) ≤ 200 := by exact_mod_cast hi
  constructor
  · positivity
  · exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 200)).mpr (by linarith)

theorem gridValues_lower {phi : ℝ → ℝ}
    (h : NormalizedNecessaryTwoClass (L : ℝ) phi) (j : Variables) :
    (lower j : ℝ) ≤ gridValues phi j := by
  have hL0 : (0 : ℝ) < L := by norm_num [L]
  have hL1 : (L : ℝ) < 1 := by norm_num [L]
  by_cases hj : j.val ≤ 200
  · have hr := grid_rank_mem hj
    have h0 := h.primitive_nonneg hL0 hL1 hr
    have hq := h.primitive_reverse_lower hr
    simp only [lower, if_pos hj, gridValues, Rat.cast_max, Rat.cast_zero, Rat.cast_sub, Q_cast, node_cast]
    apply max_le h0
    simpa [linePrimitive] using hq
  · have hjlo : 201 ≤ j.val := by omega
    have hjhi : j.val - 201 ≤ 200 := by omega
    have hr := grid_rank_mem hjhi
    have h0 := h.moment_nonneg hL0 hL1 hr
    simp only [lower, if_neg hj, gridValues]
    by_cases htr : turn < node (j.val - 201)
    · rw [if_pos htr]
      have har : ((turn : ℚ) : ℝ) ≤ ((j.val - 201 : ℕ) : ℝ) / 200 := by
        have hh : ((turn : ℚ) : ℝ) < ((node (j.val - 201) : ℚ) : ℝ) := by exact_mod_cast htr
        simpa only [node_cast] using hh.le
      have ha : (0 : ℝ) ≤ (turn : ℝ) := by norm_num [turn, L]
      have hm := h.moment_reverse_lower hL0 hL1 ha har hr.2
      simpa only [Rat.cast_sub, Rat.cast_mul, VQ_cast, Q_cast, Rat.cast_one, node_cast] using hm
    · simpa only [if_neg htr, Rat.cast_zero] using h0

theorem gridValues_upper {phi : ℝ → ℝ}
    (h : NormalizedNecessaryTwoClass (L : ℝ) phi) (j : Variables) :
    gridValues phi j ≤ (upper j : ℝ) := by
  by_cases hj : j.val ≤ 200
  · have hr := grid_rank_mem hj
    by_cases hzero : j.val = 0 ∨ j.val = 200 ∨ j.val = 201
    · rcases hzero with hz | hz | hz
      · simp [gridValues, upper, hj, hz, activationPrimitive]
      · have he : (j.val : ℝ) / 200 = 1 := by rw [hz]; norm_num
        simp [gridValues, upper, hj, hz, he, h.integral_zero]
      · omega
    · simpa only [gridValues, if_pos hj, upper, if_neg hzero, Q_cast, node_cast, linePrimitive] using h.primitive_upper hr
  · have hjhi : j.val - 201 ≤ 200 := by omega
    have hr := grid_rank_mem hjhi
    by_cases hzero : j.val = 0 ∨ j.val = 200 ∨ j.val = 201
    · rcases hzero with hz | hz | hz
      · omega
      · omega
      · simp [gridValues, upper, hj, hz, primitiveMoment]
    · simpa only [gridValues, if_neg hj, upper, if_neg hzero, VQ_cast, node_cast] using h.moment_upper hr

end OptimalG.UniversalLP
