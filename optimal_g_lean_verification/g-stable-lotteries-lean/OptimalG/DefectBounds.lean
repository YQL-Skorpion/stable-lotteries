import OptimalG.MiddleRankConvexity
import OptimalG.TailContact

/-! The convex defect estimates used in the small-mass verifier (C.22). -/
namespace OptimalG
open Set MeasureTheory

/-- The trapezoidal bound for a continuous convex function vanishing at the
left endpoint, proved directly from the chord inequality. -/
theorem convex_integral_le_triangle {e : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ConvexOn ℝ (Icc a b) e)
    (hcont : ContinuousOn e (Icc a b)) (ha : e a = 0) :
    (∫ r in a..b, e r) ≤ (b - a) * e b / 2 := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · subst b
    simp
  have hpos : 0 < b - a := sub_pos.mpr hlt
  have hchord : ∀ r ∈ Icc a b, e r ≤ ((r - a) / (b - a)) * e b := by
    intro r hr
    have hsum : (b - r) / (b - a) + (r - a) / (b - a) = 1 := by field_simp; ring
    have hh := hc.2 (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
      (div_nonneg (sub_nonneg.mpr hr.2) hpos.le)
      (div_nonneg (sub_nonneg.mpr hr.1) hpos.le) hsum
    have hid : (b - r) / (b - a) * a + (r - a) / (b - a) * b = r := by field_simp; ring
    simpa only [smul_eq_mul, hid, ha, mul_zero, zero_add] using hh
  have hi : IntervalIntegrable (fun r => (r - a) / (b - a) * e b) volume a b :=
    (by fun_prop : Continuous (fun r => (r - a) / (b - a) * e b)).intervalIntegrable a b
  have hd (r : ℝ) : HasDerivAt (fun r => (r - a) ^ 2 / (2 * (b - a)) * e b)
      ((r - a) / (b - a) * e b) r := by
    convert ((((hasDerivAt_id r).sub_const a).pow 2).div_const (2 * (b - a))).mul_const (e b) using 1 <;>
      first | rfl | (simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]; field_simp <;> ring)
  have hint : (∫ r in a..b, (r - a) / (b - a) * e b) = (b - a) * e b / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi]
    field_simp
    ring
  rw [← hint]
  exact intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable_of_Icc hab) hi hchord

noncomputable def scoreDefect (phi : ℝ → ℝ) (lam r : ℝ) : ℝ := lam - r - phi r
noncomputable def primitiveDefect (phi : ℝ → ℝ) (lam S r : ℝ) : ℝ :=
  Variational.quadratic lam r - S - curvePrimitive phi r

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem scoreDefect_nonneg {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    0 ≤ scoreDefect phi lam r := sub_nonneg.mpr (h.ceiling r hr)

theorem scoreDefect_convex (hc : ConcaveOn ℝ (Icc lam 1) phi) :
    ConvexOn ℝ (Icc lam 1) (scoreDefect phi lam) := by
  exact ((convexOn_const lam (convex_Icc lam 1)).sub (concaveOn_id (convex_Icc lam 1))).sub hc

theorem primitiveDefect_eq_integral {S a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hstart : curvePrimitive phi a = Variational.quadratic lam a - S) :
    primitiveDefect phi lam S b = ∫ r in a..b, scoreDefect phi lam r := by
  have hline : IntervalIntegrable (fun r : ℝ => lam - r) volume a b :=
    (continuous_const.sub continuous_id).intervalIntegrable a b
  have hQ : (∫ r in a..b, lam - r) = Variational.quadratic lam b - Variational.quadratic lam a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => Variational.quadratic_hasDerivAt lam r) hline
  change _ = ∫ r in a..b, (lam - r) - phi r
  rw [intervalIntegral.integral_sub hline (h.integral_subinterval ha hab hb), hQ,
    ← h.primitive_difference ha hab hb, hstart]
  unfold primitiveDefect
  ring

theorem primitiveDefect_le_triangle {S a b : ℝ} (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (ha : lam ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hstart : curvePrimitive phi a = Variational.quadratic lam a - S)
    (hzero : phi a = lam - a) :
    primitiveDefect phi lam S b ≤ (b - a) * scoreDefect phi lam b / 2 := by
  rw [h.primitiveDefect_eq_integral (h.lam_pos.le.trans ha) hab hb hstart]
  apply convex_integral_le_triangle hab
    ((h.scoreDefect_convex hc).subset (Icc_subset_Icc ha hb) (convex_Icc a b))
  · exact ((continuous_const.sub continuous_id).continuousOn.sub
      (h.continuous.mono (Icc_subset_Icc (h.lam_pos.le.trans ha) hb)))
  · simp [scoreDefect, hzero]

/-- The exact C.22 estimate before inserting a numerical lower bound on the defect. -/
theorem thirdTest_defect_bound {S a p z beta eta : ℝ}
    (hc : ConcaveOn ℝ (Icc lam 1) phi) (ha : lam ≤ a) (haz : a ≤ z) (hz : z ≤ 1)
    (hb : 0 ≤ beta)
    (hstart : curvePrimitive phi a = Variational.quadratic lam a - S)
    (hzero : phi a = lam - a)
    (hshift : curvePrimitive phi (z - p) ≤ Variational.quadratic lam (z - p) - S) :
    z - lam + beta * packingK phi p 0 z + eta * phi z ≤
      (z - lam) * (1 + beta * p - eta) - beta * p ^ 2 / 2 +
        (beta * (z - a) / 2 - eta) * scoreDefect phi lam z := by
  have hdef := h.primitiveDefect_le_triangle hc ha haz hz hstart hzero
  have hm := mul_le_mul_of_nonneg_left hdef hb
  have hs := mul_le_mul_of_nonneg_left hshift hb
  have hJ0 : curvePrimitive phi 0 = 0 := by simp [curvePrimitive]
  simp only [packingK, add_zero, hJ0, sub_zero]
  unfold primitiveDefect Variational.quadratic scoreDefect at *
  nlinarith

end VerifierCurve
end OptimalG
