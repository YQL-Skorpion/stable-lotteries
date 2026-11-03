import OptimalG.ClippedCorrection
import OptimalG.TailControl

/-! The constant correction for intermediate masses in C.24. -/
namespace OptimalG
open Set MeasureTheory

private theorem integral_reverse_ramp (x r : ℝ) :
    (∫ u in (0 : ℝ)..r, x - u) = x * r - r ^ 2 / 2 := by
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => x * u - u ^ 2 / 2) (x - u) u := by
    convert ((hasDerivAt_id u).const_mul x).sub (((hasDerivAt_id u).pow 2).div_const 2) using 1 <;>
      first | rfl | (simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((continuous_const.sub continuous_id).intervalIntegrable 0 r)]
  simp

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem primitive_low_triangle
    (hlow : ∀ a b, 0 ≤ a → a ≤ b → b ≤ lam → phi a - phi b ≤ b - a)
    {x r : ℝ} (hx : x ∈ Icc (0 : ℝ) lam) (hr : r ∈ Icc (0 : ℝ) 1) :
    curvePrimitive phi r - r * phi x ≤ x ^ 2 / 2 := by
  have hx1 := hx.2.trans h.lam_lt_one.le
  have hbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) x) :
      curvePrimitive phi s - s * phi x ≤ x * s - s ^ 2 / 2 := by
    have hi := h.integral_subinterval (a := 0) le_rfl hs.1 (hs.2.trans hx1)
    have hlin : IntervalIntegrable (fun u : ℝ => x - u) volume 0 s :=
      (continuous_const.sub continuous_id).intervalIntegrable 0 s
    have hh := intervalIntegral.integral_mono_on hs.1
      (hi.sub (intervalIntegrable_const (c := phi x))) hlin (by
        intro u hu
        exact hlow u x hu.1 (hu.2.trans hs.2) hx.2)
    rw [intervalIntegral.integral_sub hi (intervalIntegrable_const (c := phi x)),
      intervalIntegral.integral_const, integral_reverse_ramp] at hh
    simpa only [curvePrimitive, sub_zero, smul_eq_mul] using hh
  by_cases hrx : r ≤ x
  · have hh := hbound r ⟨hr.1, hrx⟩
    nlinarith [sq_nonneg (x - r)]
  · have hxbound := hbound x ⟨hx.1, le_rfl⟩
    have hh := h.primitive_increment_upper hx.1 (le_of_not_ge hrx) hr.2
    nlinarith

/-- The C.24 ratio inequality follows from a unit low-rank slope bound,
an affine end of the low segment and two scalar coefficient bounds. -/
theorem constantCorrection_ratio
    (hlow : ∀ a b, 0 ≤ a → a ≤ b → b ≤ lam → phi a - phi b ≤ b - a)
    {p beta r : ℝ} (hp : p ∈ Ioo lam 1) (hr : r ∈ Icc (0 : ℝ) lam)
    (hb : 0 ≤ beta) (hbr : beta * r ≤ 2)
    (hc : beta * curvePrimitive phi (1 - p) ≤ lam)
    (hline : ∀ x ∈ Icc r lam, phi x = lam - x) :
    ∀ x ∈ Ico (0 : ℝ) lam,
      lowRankRatio phi lam x - correctionRatio phi (lam - beta * curvePrimitive phi (1 - p)) x
        ≤ beta * (1 - p) := by
  have hh : 1 - p ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hp.2], by linarith [hp.1, h.lam_pos]⟩
  have hsmall (x : ℝ) (hx : x ∈ Icc (0 : ℝ) r) :
      0 ≤ x + beta * (1 - p) * phi x - beta * curvePrimitive phi (1 - p) := by
    have htri := mul_le_mul_of_nonneg_left
      (h.primitive_low_triangle hlow ⟨hx.1, hx.2.trans hr.2⟩ hh) hb
    have hbx := (mul_le_mul_of_nonneg_left hx.2 hb).trans hbr
    have hm := mul_nonneg hx.1 (show 0 ≤ 2 - beta * x by linarith)
    nlinarith
  intro x hx
  have hmain : 0 ≤ x + beta * (1 - p) * phi x - beta * curvePrimitive phi (1 - p) := by
    by_cases hxr : x ≤ r
    · exact hsmall x ⟨hx.1, hxr⟩
    · have hleft := hsmall r ⟨hr.1, le_rfl⟩
      rw [hline r ⟨le_rfl, hr.2⟩] at hleft
      have hright : 0 ≤ lam + beta * (1 - p) * (lam - lam) - beta * curvePrimitive phi (1 - p) := by linarith
      have ha := mul_nonneg (show 0 ≤ lam - x by linarith [hx.2]) hleft
      have hb' := mul_nonneg (show 0 ≤ x - r by linarith) hright
      have hrlt : 0 < lam - r := by linarith [hx.2]
      rw [hline x ⟨le_of_not_ge hxr, hx.2.le⟩]
      apply nonneg_of_mul_nonneg_right (a := lam - r) ?_ hrlt
      nlinarith
  unfold lowRankRatio correctionRatio
  rw [← sub_div, div_le_iff₀ (h.positive hx)]
  linarith

theorem highMassTest_constantCorrection {p beta eta : ℝ}
    (hp : p ∈ Ioo lam 1) (hb : 0 ≤ beta)
    (hnorm : beta * curvePrimitive phi p = p)
    (hc : beta * curvePrimitive phi (1 - p) ≤ lam)
    (hfirst : ∀ q ∈ Icc (0 : ℝ) lam,
      q + beta * packingDelta phi p q ≤ beta * curvePrimitive phi (1 - p))
    (hratio : ∀ x ∈ Ico (0 : ℝ) lam,
      lowRankRatio phi lam x - correctionRatio phi (lam - beta * curvePrimitive phi (1 - p)) x
        ≤ beta * (1 - p))
    (heta : ∀ x ∈ Ico (0 : ℝ) lam,
      eta ≤ lowRankRatio phi lam x + correctionRatio phi (lam - beta * curvePrimitive phi (1 - p)) x)
    (hmixed : ∀ q ∈ Icc (0 : ℝ) lam, ∀ z ∈ Icc p 1,
      z + q - lam + beta * packingK phi p q z + eta * phi z ≤ 0) :
    HighMassTest phi lam p beta (fun _ => lam - beta * curvePrimitive phi (1 - p)) := by
  constructor
  · exact hb
  · intro x hx; linarith
  · exact hnorm
  · intro x hx q hq hqx
    have hh := hfirst q ⟨hq, hqx.trans hx.2.le⟩
    linarith
  · intro q hq
    exact (hfirst q hq).trans hc
  · exact hratio
  · intro x hx q hq z hz
    have hh := mul_le_mul_of_nonpos_right (heta x hx) (h.nonpositive ⟨hp.1.le.trans hz.1, hz.2⟩)
    linarith [hmixed q hq z hz]

end VerifierCurve
end OptimalG
