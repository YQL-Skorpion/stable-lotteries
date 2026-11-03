import OptimalG.Certificates.ExpressionTaylorResidual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! A genuine midpoint quadrature error bound for the reference-cell integrals. -/
namespace OptimalG.Certificates
open Set MeasureTheory

private theorem midpoint_polynomial_integral (a b B : ℝ) :
    (∫ t in (0:ℝ)..1,a+b*(t-1/2)-B*(t-1/2)^2/2)=a-B/24 := by
  let F := fun t : ℝ => a*t+b*(t-1/2)^2/2-B*(t-1/2)^3/6
  have hd (t : ℝ) : HasDerivAt F (a+b*(t-1/2)-B*(t-1/2)^2/2) t := by
    convert! (((hasDerivAt_id t).const_mul a).add
      (((((hasDerivAt_id t).sub_const (1/2)).pow 2).const_mul b).div_const 2)).sub
        (((((hasDerivAt_id t).sub_const (1/2)).pow 3).const_mul B).div_const 6) using 1 <;>
      first | rfl | (funext x; dsimp [F]; ring) | (simp only [Pi.sub_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((by fun_prop : Continuous (fun t : ℝ => a+b*(t-1/2)-B*(t-1/2)^2/2)).intervalIntegrable 0 1)]
  dsimp [F]
  ring

/-- One-sided midpoint quadrature, using the actual second derivative. -/
theorem midpoint_integral_lower {f f' f'' : ℝ → ℝ} {B : ℝ}
    (hf : ∀ t ∈ Icc (0:ℝ) 1,HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc (0:ℝ) 1,HasDerivAt f' (f'' t) t)
    (hsecond : ∀ t ∈ Icc (0:ℝ) 1,-B≤f'' t) :
    f (1/2)-B/24≤∫ t in (0:ℝ)..1,f t := by
  have hi : IntervalIntegrable f volume 0 1 :=
    (show ContinuousOn f (Icc (0:ℝ) 1) from fun t ht => (hf t ht).continuousAt.continuousWithinAt).intervalIntegrable_of_Icc (by norm_num)
  have hh := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1)
    ((by fun_prop : Continuous (fun t : ℝ => f (1/2)+f' (1/2)*(t-1/2)-B*(t-1/2)^2/2)).intervalIntegrable 0 1)
    hi (fun t ht => second_order_from_midpoint_lower hf hf' hsecond ht)
  simpa only [midpoint_polynomial_integral] using hh

/-- The midpoint rule error is at most one twenty-fourth of the actual
uniform absolute second-derivative bound. -/
theorem midpoint_integral_abs_error {f f' f'' : ℝ → ℝ} {B : ℝ}
    (hf : ∀ t ∈ Icc (0:ℝ) 1,HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc (0:ℝ) 1,HasDerivAt f' (f'' t) t)
    (hsecond : ∀ t ∈ Icc (0:ℝ) 1,|f'' t|≤B) :
    |(∫ t in (0:ℝ)..1,f t)-f (1/2)|≤B/24 := by
  have hlo := midpoint_integral_lower hf hf' (fun t ht => (abs_le.mp (hsecond t ht)).1)
  have hhi := midpoint_integral_lower (fun t ht => (hf t ht).neg)
    (fun t ht => (hf' t ht).neg) (fun t ht => show -B≤ -f'' t by linarith only [(abs_le.mp (hsecond t ht)).2])
  simp only [Pi.neg_apply,intervalIntegral.integral_neg] at hhi
  exact abs_le.mpr ⟨by linarith only [hlo],by linarith only [hhi]⟩

end OptimalG.Certificates
