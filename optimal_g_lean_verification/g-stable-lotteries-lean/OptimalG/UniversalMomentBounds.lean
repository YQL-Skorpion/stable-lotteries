import OptimalG.NecessaryPrimitiveBounds

/-! Actual integral moment bounds underlying the universal LP's basic rows. -/
namespace OptimalG
open Set MeasureTheory

noncomputable def primitiveMoment (phi : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..r, activationPrimitive phi t

noncomputable def linePrimitive (L r : ℝ) : ℝ := L * r - r ^ 2 / 2
noncomputable def lineMoment (L r : ℝ) : ℝ := L * r ^ 2 / 2 - r ^ 3 / 6

theorem lineMoment_hasDerivAt (L r : ℝ) :
    HasDerivAt (lineMoment L) (linePrimitive L r) r := by
  have hh := (((hasDerivAt_pow 2 r).const_mul L).div_const 2).sub
    ((hasDerivAt_pow 3 r).div_const 6)
  convert hh using 1 <;> first | rfl | (simp [linePrimitive]; ring)

theorem linePrimitive_integral (L a b : ℝ) :
    (∫ r in a..b, linePrimitive L r) = lineMoment L b - lineMoment L a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => lineMoment_hasDerivAt L r)
    ((by unfold linePrimitive; fun_prop : Continuous (linePrimitive L)).intervalIntegrable a b)

theorem shifted_linePrimitive_integral (L a b c : ℝ) :
    (∫ r in a..b, c + linePrimitive L r) = (b - a) * c + lineMoment L b - lineMoment L a := by
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((by unfold linePrimitive; fun_prop : Continuous (linePrimitive L)).intervalIntegrable a b),
    intervalIntegral.integral_const, linePrimitive_integral]
  simp only [smul_eq_mul]
  ring

namespace NormalizedNecessaryTwoClass
variable {L : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass L phi)
include h

theorem primitive_nonneg (hL0 : 0 < L) (hL1 : L < 1) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    0 ≤ activationPrimitive phi r := by
  by_cases h0 : r = 0
  · simp [h0, activationPrimitive]
  by_cases h1 : r = 1
  · rw [h1, h.integral_zero]
  exact (h.primitive_pos hL0 hL1 r ⟨lt_of_le_of_ne hr.1 (Ne.symm h0), lt_of_le_of_ne hr.2 h1⟩).le

theorem moment_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    primitiveMoment phi b - primitiveMoment phi a = ∫ r in a..b, activationPrimitive phi r := by
  have ha' := (h.primitive_continuous.mono (Icc_subset_Icc le_rfl (hab.trans hb))).intervalIntegrable_of_Icc (μ := volume) ha
  have hab' := (h.primitive_continuous.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc (μ := volume) hab
  have hh := intervalIntegral.integral_add_adjacent_intervals ha' hab'
  unfold primitiveMoment
  linarith

theorem moment_bin_upper {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    primitiveMoment phi b - primitiveMoment phi a ≤
      (b - a) * (activationPrimitive phi a - linePrimitive L a) + lineMoment L b - lineMoment L a := by
  rw [h.moment_increment ha hab hb]
  have hi := (h.primitive_continuous.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc (μ := volume) hab
  have hg : Continuous (fun r => activationPrimitive phi a - linePrimitive L a + linePrimitive L r) := by
    unfold linePrimitive
    fun_prop
  have hh := intervalIntegral.integral_mono_on hab hi (hg.intervalIntegrable a b) (fun r hr => ?_)
  · simpa only [shifted_linePrimitive_integral] using hh
  · have hh := h.primitive_increment_ceiling ha hr.1 (hr.2.trans hb)
    unfold linePrimitive
    linarith

theorem moment_bin_lower {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (b - a) * (activationPrimitive phi b - linePrimitive L b) + lineMoment L b - lineMoment L a ≤
      primitiveMoment phi b - primitiveMoment phi a := by
  rw [h.moment_increment ha hab hb]
  have hi := (h.primitive_continuous.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc (μ := volume) hab
  have hg : Continuous (fun r => activationPrimitive phi b - linePrimitive L b + linePrimitive L r) := by
    unfold linePrimitive
    fun_prop
  have hh := intervalIntegral.integral_mono_on hab (hg.intervalIntegrable a b) hi (fun r hr => ?_)
  · simpa only [shifted_linePrimitive_integral] using hh
  · have hh := h.primitive_increment_ceiling (ha.trans hr.1) hr.2 hb
    unfold linePrimitive
    linarith

theorem moment_upper {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    primitiveMoment phi r ≤ lineMoment L r := by
  have hh := h.moment_bin_upper (a := 0) le_rfl hr.1 hr.2
  simpa [activationPrimitive, primitiveMoment, linePrimitive, lineMoment] using hh

theorem moment_nonneg (hL0 : 0 < L) (hL1 : L < 1) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    0 ≤ primitiveMoment phi r := by
  exact intervalIntegral.integral_nonneg hr.1
    (fun t ht => h.primitive_nonneg hL0 hL1 ⟨ht.1, ht.2.trans hr.2⟩)

theorem moment_reverse_lower (hL0 : 0 < L) (hL1 : L < 1)
    {a r : ℝ} (ha : 0 ≤ a) (har : a ≤ r) (hr : r ≤ 1) :
    lineMoment L r - lineMoment L a - linePrimitive L 1 * (r - a) ≤ primitiveMoment phi r := by
  have hi := (h.primitive_continuous.mono (Icc_subset_Icc ha hr)).intervalIntegrable_of_Icc (μ := volume) har
  have hg : Continuous (fun t => -linePrimitive L 1 + linePrimitive L t) := by
    unfold linePrimitive
    fun_prop
  have hb := intervalIntegral.integral_mono_on har (hg.intervalIntegrable a r) hi (fun t ht => ?_)
  · rw [shifted_linePrimitive_integral, ← h.moment_increment ha har hr] at hb
    have hma := h.moment_nonneg hL0 hL1 ⟨ha, har.trans hr⟩
    linarith
  · have hh := h.primitive_reverse_lower ⟨ha.trans ht.1, ht.2.trans hr⟩
    unfold linePrimitive
    nlinarith

end NormalizedNecessaryTwoClass
end OptimalG
