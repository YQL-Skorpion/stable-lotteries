import OptimalG.SplitBounds

/-! The first C.3 split reduction: a scalar derivative margin and the q=0
binary test imply every low split. No derivative of the completed curve is used. -/
namespace OptimalG
open Set MeasureTheory

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem normalized_binary_gap_of_primitive {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hmargin : curvePrimitive phi p ≤ p*(phi 0-lam+1-p)) :
    1 ≤ (p/curvePrimitive phi p)*(phi 0-lam+1-p) := by
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (h.primitive_pos hp)).mpr
  simpa only [one_mul] using hmargin

theorem normalized_binary_gap_small {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hsmall : p ≤ 1-lam) :
    1 ≤ (p/curvePrimitive phi p)*(phi 0-lam+1-p) := by
  apply h.normalized_binary_gap_of_primitive hp
  have hh := h.primitive_increment_upper (a := 0) le_rfl hp.1.le hp.2.le
  have hz : curvePrimitive phi 0=0 := by simp [curvePrimitive]
  rw [hz,sub_zero] at hh
  have hm := mul_nonneg hp.1.le (show 0 ≤ 1-lam-p by linarith)
  nlinarith only [hh,hm]

theorem normalized_binary_gap_flat {p S : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hflat : curvePrimitive phi p=lam*p-p^2/2-S)
    (hmargin : 0 ≤ p*(1+phi 0-2*lam)-p^2/2+S) :
    1 ≤ (p/curvePrimitive phi p)*(phi 0-lam+1-p) := by
  apply h.normalized_binary_gap_of_primitive hp
  rw [hflat]
  nlinarith only [hmargin]

theorem normalized_binary_le_zero_split {p q : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hlow : ∀ u ∈ Icc (0 : ℝ) lam,phi 0-u ≤ phi u)
    (hgap : 1 ≤ (p/curvePrimitive phi p)*(phi 0-lam+1-p))
    (hq : 0 ≤ q) (hqp : q ≤ p) (hql : q ≤ lam) :
    q+(p/curvePrimitive phi p)*packingDelta phi p q ≤
      (p/curvePrimitive phi p)*curvePrimitive phi (1-p) := by
  have hb : 0 ≤ p/curvePrimitive phi p := (div_pos hp.1 (h.primitive_pos hp)).le
  have hh := h.testValue_le_zero_split hlow hq hqp hql hp.2.le le_rfl hb hgap
  have hzero : curvePrimitive phi 0=0 := by simp [curvePrimitive]
  have hone : curvePrimitive phi 1=0 := h.integral_zero
  simpa only [packingK,packingDelta,hzero,hone,sub_zero,add_zero] using hh

theorem normalized_binary_of_zero_split {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hlow : ∀ u ∈ Icc (0 : ℝ) lam,phi 0-u ≤ phi u)
    (hgap : 1 ≤ (p/curvePrimitive phi p)*(phi 0-lam+1-p))
    (hzero : p*curvePrimitive phi (1-p) ≤ lam*curvePrimitive phi p) :
    ∀ q,0 ≤ q → q ≤ p → q ≤ lam →
      q+(p/curvePrimitive phi p)*packingDelta phi p q ≤ lam := by
  intro q hq hqp hql
  apply (h.normalized_binary_le_zero_split hp hlow hgap hq hqp hql).trans
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (h.primitive_pos hp)).mpr hzero

end VerifierCurve
end OptimalG
