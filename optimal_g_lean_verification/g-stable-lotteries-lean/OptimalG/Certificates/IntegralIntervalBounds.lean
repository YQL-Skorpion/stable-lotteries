import OptimalG.Certificates.CumulativeIntegral

/-! Integer interval wrappers for genuine cell integrals and their partial
suffixes. Together with CumulativeIntegral these bound every future integral. -/
namespace OptimalG.Certificates.IntegerInterval
open Set MeasureTheory

def integralCheck (s : ℕ) (a b : ℚ) (bound out : IntegerInterval) : Bool :=
  constCheck s ((b-a)*(bound.lo:ℚ)/s) out &&
    constCheck s ((b-a)*(bound.hi:ℚ)/s) out

def partialIntegralCheck (s : ℕ) (a b : ℚ) (bound out : IntegerInterval) : Bool :=
  constCheck s (min 0 ((b-a)*(bound.lo:ℚ)/s)) out &&
    constCheck s (max 0 ((b-a)*(bound.hi:ℚ)/s)) out

theorem integralCheck_sound {s : ℕ} (hs : 0<s) {a b : ℚ}
    {bound out : IntegerInterval} (hc : integralCheck s a b bound out=true)
    (hab : a≤b) {f : ℝ→ℝ} (hf : IntervalIntegrable f volume (a:ℝ) b)
    (hb : ∀ᵐ x ∂volume.restrict (Icc (a:ℝ) b),bound.Contains s (f x)) :
    out.Contains s (∫ x in (a:ℝ)..b,f x) := by
  have hab' : (a:ℝ)≤b := by exact_mod_cast hab
  have hlo := intervalIntegral.integral_mono_ae_restrict hab'
    (intervalIntegrable_const (c:=(bound.lo:ℝ)/(s:ℝ))) hf
    (hb.mono fun x hx => lower_bound hs hx)
  have hhi := intervalIntegral.integral_mono_ae_restrict hab' hf
    (intervalIntegrable_const (c:=(bound.hi:ℝ)/(s:ℝ)))
    (hb.mono fun x hx => upper_bound hs hx)
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hlo hhi
  obtain ⟨hl,hu⟩ := Bool.and_eq_true_iff.mp hc
  have hl' := constCheck_sound hl
  have hu' := constCheck_sound hu
  simp only [Rat.cast_div,Rat.cast_mul,Rat.cast_sub,Rat.cast_intCast,Rat.cast_natCast] at hl' hu'
  refine ⟨?_,?_⟩
  · exact hl'.1.trans (mul_le_mul_of_nonneg_left (by simpa only [mul_div_assoc] using hlo) (Nat.cast_nonneg s))
  · exact (mul_le_mul_of_nonneg_left (by simpa only [mul_div_assoc] using hhi) (Nat.cast_nonneg s)).trans hu'.2

theorem partialIntegralCheck_sound {s : ℕ} (hs : 0<s) {a b : ℚ}
    {bound out : IntegerInterval} (hc : partialIntegralCheck s a b bound out=true)
    {f : ℝ→ℝ} {r : ℝ} (hr : r∈Icc (a:ℝ) b)
    (hf : IntervalIntegrable f volume (a:ℝ) b)
    (hb : ∀ᵐ x ∂volume.restrict (Icc (a:ℝ) b),bound.Contains s (f x)) :
    out.Contains s (∫ x in r..b,f x) := by
  have h := partial_cell_integral_bounds hr hf
    (hb.mono fun x hx => And.intro (lower_bound hs hx) (upper_bound hs hx))
  obtain ⟨hl,hu⟩ := Bool.and_eq_true_iff.mp hc
  have hl' := constCheck_sound hl
  have hu' := constCheck_sound hu
  simp only [Rat.cast_min,Rat.cast_max,Rat.cast_zero,Rat.cast_div,Rat.cast_mul,
    Rat.cast_sub,Rat.cast_intCast,Rat.cast_natCast] at hl' hu'
  refine ⟨?_,?_⟩
  · exact hl'.1.trans (mul_le_mul_of_nonneg_left (by simpa only [mul_div_assoc] using h.1) (Nat.cast_nonneg s))
  · exact (mul_le_mul_of_nonneg_left (by simpa only [mul_div_assoc] using h.2) (Nat.cast_nonneg s)).trans hu'.2

/-- A partial-cell enclosure plus the checked future interval encloses the
actual cumulative potential at every point, including cell endpoints. -/
theorem cumulative_contains {s : ℕ} (hs : 0<s) {a b : ℚ}
    {bound partialBox future out : IntegerInterval}
    (hpartial : partialIntegralCheck s a b bound partialBox=true)
    (hadd : (partialBox.addRounded future).subsetCheck out=true)
    {f : ℝ→ℝ} {r finish : ℝ} (hr : r∈Icc (a:ℝ) b)
    (hf : IntervalIntegrable f volume (a:ℝ) b)
    (hfuture : IntervalIntegrable f volume (b:ℝ) finish)
    (hb : ∀ᵐ x ∂volume.restrict (Icc (a:ℝ) b),bound.Contains s (f x))
    (hF : future.Contains s (∫ x in (b:ℝ)..finish,f x)) :
    out.Contains s (∫ x in r..finish,f x) := by
  have hpart := partialIntegralCheck_sound hs hpartial hr hf hb
  have hab : (a:ℝ)≤b := hr.1.trans hr.2
  have hi : IntervalIntegrable f volume r b := hf.mono_set (by
    rw [uIcc_of_le hr.2,uIcc_of_le hab]
    exact Icc_subset_Icc hr.1 le_rfl)
  have hsum := addRounded_contains hpart hF
  rw [intervalIntegral.integral_add_adjacent_intervals hi hfuture] at hsum
  exact subsetCheck_sound hsum hadd

end OptimalG.Certificates.IntegerInterval
