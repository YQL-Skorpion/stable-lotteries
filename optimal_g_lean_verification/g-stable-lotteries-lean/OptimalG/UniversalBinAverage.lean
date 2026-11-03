import OptimalG.UniversalMomentBounds

/-! Elementary interval averages used by the universal finite LP. -/
namespace OptimalG
open Set MeasureTheory

noncomputable def binAverage (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (∫ r in a..b, f r) / (b - a)

theorem binAverage_add {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    binAverage (fun r => f r + g r) a b = binAverage f a b + binAverage g a b := by
  simp only [binAverage, intervalIntegral.integral_add hf hg, add_div]

theorem binAverage_sub {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    binAverage (fun r => f r - g r) a b = binAverage f a b - binAverage g a b := by
  simp only [binAverage, intervalIntegral.integral_sub hf hg, sub_div]

theorem binAverage_const_mul (c : ℝ) (f : ℝ → ℝ) (a b : ℝ) :
    binAverage (fun r => c * f r) a b = c * binAverage f a b := by
  simp only [binAverage, intervalIntegral.integral_const_mul]
  ring

theorem binAverage_mul_const (f : ℝ → ℝ) (c a b : ℝ) :
    binAverage (fun r => f r * c) a b = binAverage f a b * c := by
  simp only [binAverage, intervalIntegral.integral_mul_const]
  ring

theorem binAverage_const (c : ℝ) {a b : ℝ} (hab : a < b) :
    binAverage (fun _ => c) a b = c := by
  simp only [binAverage, intervalIntegral.integral_const, smul_eq_mul]
  exact mul_div_cancel_left₀ c (ne_of_gt (sub_pos.mpr hab))

theorem binAverage_id {a b : ℝ} (hab : a < b) :
    binAverage (fun r : ℝ => r) a b = (a + b) / 2 := by
  rw [binAverage, integral_id]
  field_simp [ne_of_gt (sub_pos.mpr hab)]
  ring

theorem binAverage_mono {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (hle : ∀ r ∈ Icc a b, f r ≤ g r) : binAverage f a b ≤ binAverage g a b :=
  div_le_div_of_nonneg_right (intervalIntegral.integral_mono_on hab.le hf hg hle)
    (sub_pos.mpr hab).le

theorem binAverage_nonpos {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hle : ∀ r ∈ Icc a b, f r ≤ 0) :
    binAverage f a b ≤ 0 := by
  have hh := binAverage_mono hab hf intervalIntegrable_const hle
  simpa only [binAverage_const 0 hab] using hh

theorem binAverage_affine {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (A B C : ℝ) :
    binAverage (fun r => A * f r + B * r + C) a b =
      A * binAverage f a b + B * ((a + b) / 2) + C := by
  have hi : IntervalIntegrable (fun r : ℝ => r) volume a b := continuous_id.intervalIntegrable a b
  rw [binAverage_add (g := fun _ => C) ((hf.const_mul A).add (hi.const_mul B)) intervalIntegrable_const,
    binAverage_add (hf.const_mul A) (hi.const_mul B),
    binAverage_const_mul, binAverage_const_mul, binAverage_const C hab, binAverage_id hab]

theorem binAverage_affine_nonpos {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (A B C : ℝ)
    (hrow : ∀ r ∈ Icc a b, A * f r + B * r + C ≤ 0) :
    A * binAverage f a b + B * ((a + b) / 2) + C ≤ 0 := by
  rw [← binAverage_affine hab hf]
  exact binAverage_nonpos hab (((hf.const_mul A).add
    ((continuous_id.intervalIntegrable a b).const_mul B)).add intervalIntegrable_const) hrow

theorem binAverage_linear3 {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (A B C D : ℝ) :
    binAverage (fun r => A * f r + B * g r + C * r + D) a b =
      A * binAverage f a b + B * binAverage g a b + C * ((a + b) / 2) + D := by
  have hi : IntervalIntegrable (fun r : ℝ => r) volume a b := continuous_id.intervalIntegrable a b
  rw [binAverage_add (g := fun _ => D) (((hf.const_mul A).add (hg.const_mul B)).add
      (hi.const_mul C)) intervalIntegrable_const,
    binAverage_add ((hf.const_mul A).add (hg.const_mul B)) (hi.const_mul C),
    binAverage_add (hf.const_mul A) (hg.const_mul B),
    binAverage_const_mul, binAverage_const_mul, binAverage_const_mul,
    binAverage_const D hab, binAverage_id hab]

theorem binAverage_linear3_nonpos {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (A B C D : ℝ)
    (hrow : ∀ r ∈ Icc a b, A * f r + B * g r + C * r + D ≤ 0) :
    A * binAverage f a b + B * binAverage g a b + C * ((a + b) / 2) + D ≤ 0 := by
  rw [← binAverage_linear3 hab hf hg]
  exact binAverage_nonpos hab ((((hf.const_mul A).add (hg.const_mul B)).add
    ((continuous_id.intervalIntegrable a b).const_mul C)).add intervalIntegrable_const) hrow

end OptimalG
