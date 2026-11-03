import OptimalG.HighMassTest
import OptimalG.MiddleRankConvexity
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Analytic verification near mass one, including the exact margin in C.28. -/
namespace OptimalG
open Set MeasureTheory

theorem largeMass_end_coefficient {h : ℝ} (hh : 0 < h) (hhi : h ≤ 3 / 40) :
    7 - (1 - h) * (1 - 5 * h) / h ≤ -(17 / 24 : ℝ) := by
  apply (le_of_sub_nonpos ?_)
  apply (nonpos_of_mul_nonpos_right (a := h) ?_ hh)
  have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hhi)
    (show 0 ≤ (40 : ℝ) / 3 - 5 * h by linarith)
  have hc : h * (7 - (1 - h) * (1 - 5 * h) / h - -(17 / 24 : ℝ)) =
      (h - 3 / 40) * (40 / 3 - 5 * h) := by field_simp; ring
  rw [hc]
  exact hp

private theorem affine_gap_integral (h d : ℝ) :
    (∫ t in (0 : ℝ)..d, 1 - h - 8 * (d - t)) = d * (1 - h) - 4 * d ^ 2 := by
  let F := fun t : ℝ => (1 - h - 8 * d) * t + 4 * t ^ 2
  have hF (t : ℝ) : HasDerivAt F (1 - h - 8 * (d - t)) t := by
    have hd := ((hasDerivAt_id t).const_mul (1 - h - 8 * d)).add
      (((hasDerivAt_id t).pow 2).const_mul 4)
    convert hd using 1 <;> first | rfl | (simp only [id_eq, mul_one, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
  have hint : IntervalIntegrable (fun t : ℝ => 1 - h - 8 * (d - t)) volume 0 d :=
    (by fun_prop : Continuous (fun t : ℝ => 1 - h - 8 * (d - t))).intervalIntegrable 0 d
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) hint]
  dsimp [F]
  ring

/-- With the tail slope bound and the straight low segment, all mixed tests for
p≥0.925 follow analytically from the two-class test at z=1. -/
theorem mixedTest_near_one {phi : ℝ → ℝ} {lam p : ℝ} (h : VerifierCurve phi lam)
    (hp : p ∈ Ico (37 / 40 : ℝ) 1) (hlp : lam < p)
    (hline : phi (lam + (1 - p)) = -(1 - p))
    (htail : ∀ u ∈ Icc p 1, phi u ≤ -1 + 8 * (1 - u))
    (hbinary : ∀ q ∈ Icc (0 : ℝ) lam, q + (p / curvePrimitive phi p) * packingDelta phi p q ≤ lam) :
    ∀ q ∈ Icc (0 : ℝ) lam, ∀ z ∈ Icc p 1,
      z + q - lam + (p / curvePrimitive phi p) * packingK phi p q z + phi z ≤ 0 := by
  intro q hq z hz
  let beta := p / curvePrimitive phi p
  let hmass := 1 - p
  let d := 1 - z
  have hp0 : 0 < p := by linarith [hp.1]
  have hmasspos : 0 < hmass := sub_pos.mpr hp.2
  have hmasshi : hmass ≤ 3 / 40 := by dsimp [hmass]; linarith [hp.1]
  have hd : 0 ≤ d := sub_nonneg.mpr hz.2
  have hdh : d ≤ hmass := by dsimp [d, hmass]; linarith [hz.1]
  have hJpos := h.primitive_pos ⟨hp0, hp.2⟩
  have hJupper := h.primitive_le_tail ⟨hp0.le, hp.2.le⟩
  have hbeta : 0 ≤ beta := (div_pos hp0 hJpos).le
  have hbetalo : (1 - hmass) / hmass ≤ beta := by
    have hh := div_le_div_of_nonneg_left hp0.le hJpos hJupper
    simpa only [hmass, sub_sub_cancel] using hh
  have hq1 : q ≤ 1 := hq.2.trans h.lam_lt_one.le
  have hz0 : 0 ≤ z := hp0.le.trans hz.1
  have hr0 : 0 ≤ z - p + q := by linarith [hz.1, hq.1]
  have hrd : z - p + q + d ≤ 1 := by dsimp [d]; linarith [hq.2]
  have hzd : z + d ≤ 1 := by dsimp [d]; linarith
  have hint1 := h.shift_integrable hr0 hd hrd
  have hint2 := h.shift_integrable hz0 hd hzd
  have hlinint : IntervalIntegrable (fun t : ℝ => 1 - hmass - 8 * (d - t)) volume 0 d :=
    (by fun_prop : Continuous (fun t : ℝ => 1 - hmass - 8 * (d - t))).intervalIntegrable 0 d
  have hintbound := intervalIntegral.integral_mono_on hd hlinint (hint1.sub hint2) (by
    intro t ht
    have htarg : z - p + q + t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have htarget : lam + hmass ∈ Icc (0 : ℝ) 1 := ⟨by linarith [h.lam_pos], by dsimp [hmass]; linarith⟩
    have hphi := h.decreasing.antitoneOn htarg htarget (by dsimp [d, hmass] at *; linarith [ht.2, hq.2])
    change phi (lam + (1 - p)) ≤ _ at hphi
    rw [hline] at hphi
    have hupper := htail (z + t) ⟨by linarith [hz.1, ht.1], by dsimp [d] at *; linarith [ht.2]⟩
    dsimp [hmass, d]
    linarith)
  rw [affine_gap_integral, intervalIntegral.integral_sub hint1 hint2,
    h.shift_integral hr0 hd hrd, h.shift_integral hz0 hd hzd] at hintbound
  have heq1 : z - p + q + d = 1 - p + q := by dsimp [d]; ring
  have heq2 : z + d = 1 := by dsimp [d]; ring
  have hJ1 : curvePrimitive phi 1 = 0 := h.integral_zero
  rw [heq1, heq2, hJ1] at hintbound
  have hscaled := mul_le_mul_of_nonneg_left hintbound hbeta
  have hbinaryq := hbinary q hq
  have htailz := htail z hz
  have hcoeff := largeMass_end_coefficient hmasspos hmasshi
  have hpositive : 0 ≤ 1 - 5 * hmass := by linarith
  have hb1 := mul_le_mul_of_nonneg_right hbetalo hpositive
  have hb2 := mul_le_mul_of_nonneg_left (show 1 - 5 * hmass ≤ 1 - hmass - 4 * d by linarith) hbeta
  have hco : 7 - beta * (1 - hmass - 4 * d) ≤ -(17 / 24 : ℝ) := by
    have hid : (1 - hmass) / hmass * (1 - 5 * hmass) =
        (1 - hmass) * (1 - 5 * hmass) / hmass := by ring
    rw [hid] at hb1
    linarith
  have hfinal := mul_le_mul_of_nonneg_left hco hd
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos hd (by norm_num : -(17 / 24 : ℝ) ≤ 0)
  change z + q - lam + beta * packingK phi p q z + phi z ≤ 0
  change q + beta * packingDelta phi p q ≤ lam at hbinaryq
  unfold packingDelta packingK at *
  dsimp [d, hmass] at *
  nlinarith

end OptimalG
