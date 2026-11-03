import OptimalG.HighMassTest
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Integral and algebraic estimates for the clipped correction of C.25. -/
namespace OptimalG
open Set MeasureTheory

private theorem integral_affine_ramp (a b : ℝ) :
    (∫ s in a..b, s - a) = (b - a) ^ 2 / 2 := by
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => (s - a) ^ 2 / 2) (s - a) s := by
    convert (((hasDerivAt_id s).sub_const a).pow 2).div_const 2 using 1 <;>
      first | rfl | (simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((continuous_id.sub continuous_const).intervalIntegrable a b)]
  simp

theorem integral_positive_ramp {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ s in (0 : ℝ)..b, max (s - a) 0) = (max (b - a) 0) ^ 2 / 2 := by
  by_cases hba : b ≤ a
  · rw [max_eq_right (sub_nonpos.mpr hba)]
    have heq : (∫ s in (0 : ℝ)..b, max (s - a) 0) = ∫ _s in (0 : ℝ)..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hb] at hs
      exact max_eq_right (by linarith [hs.2])
    simp [heq]
  · have hab := le_of_lt (lt_of_not_ge hba)
    have hi : Continuous (fun s : ℝ => max (s - a) 0) := by fun_prop
    have hfirst : (∫ s in (0 : ℝ)..a, max (s - a) 0) = 0 := by
      calc
        _ = ∫ _s in (0 : ℝ)..a, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le ha] at hs
          exact max_eq_right (sub_nonpos.mpr hs.2)
        _ = 0 := by simp
    have hsecond : (∫ s in a..b, max (s - a) 0) = (b - a) ^ 2 / 2 := by
      calc
        _ = ∫ s in a..b, s - a := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le hab] at hs
          exact max_eq_left (sub_nonneg.mpr hs.1)
        _ = _ := integral_affine_ramp a b
    have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hi.intervalIntegrable 0 a) (hi.intervalIntegrable a b)
    rw [hfirst, hsecond, zero_add] at hh
    rw [max_eq_left (sub_nonneg.mpr hab)]
    exact hh.symm

/-- The two elementary cases in the rearrangement bound of C.25. -/
theorem clipped_rearrangement_nonpos {h v w beta t : ℝ}
    (hh : 0 ≤ h) (hv : 0 ≤ v) (hw : w ∈ Icc (0 : ℝ) v)
    (hb : 0 ≤ beta) (ht : t = beta * h) (htwo : t ≤ 2)
    (hshort : (t - 1) * v ≤ t * h / 2) :
    (t - 1) * v - t * w - beta / 2 *
      ((max (h - w) 0) ^ 2 - (max (h - v) 0) ^ 2) ≤ 0 := by
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  by_cases hvh : v ≤ h
  · rw [max_eq_left (by linarith [hw.2]), max_eq_left (sub_nonneg.mpr hvh)]
    have hbv : beta * v ≤ 2 := (mul_le_mul_of_nonneg_left hvh hb).trans (by simpa [ht] using htwo)
    have hx := mul_nonpos_of_nonneg_of_nonpos hv (show beta * v - 2 ≤ 0 by linarith)
    have hy := mul_nonneg hb (sq_nonneg w)
    rw [ht]
    nlinarith
  · rw [max_eq_right (show h - v ≤ 0 by linarith)]
    by_cases hwh : h ≤ w
    · rw [max_eq_right (sub_nonpos.mpr hwh)]
      have hx := mul_le_mul_of_nonneg_left hwh ht0
      nlinarith [mul_nonneg ht0 hh]
    · rw [max_eq_left (by linarith)]
      have hy := mul_nonneg hb (sq_nonneg w)
      rw [ht] at hshort ⊢
      nlinarith

/-- The tail slope estimate used in the paper implies both short-split
conditions uniformly up to x-q=0.18. -/
theorem clipped_short_conditions {h t : ℝ} (hh : h ∈ Icc (0 : ℝ) (3 / 25))
    (ht : 0 ≤ t) (hupper : t ≤ (1 - h) / (1 - 67 * h / 20)) :
    t ≤ 2 ∧ ∀ v ∈ Icc (0 : ℝ) (9 / 50), (t - 1) * v ≤ t * h / 2 := by
  have hden : 0 < 1 - 67 * h / 20 := by linarith [hh.2]
  have hmul := (le_div_iff₀ hden).mp hupper
  have ht3 : t ≤ 3 / 2 := by
    by_contra hn
    have hh' := mul_pos (show 0 < t - 3 / 2 by linarith) hden
    nlinarith [hh.2]
  refine ⟨by linarith, ?_⟩
  intro v hv
  by_cases ht1 : t ≤ 1
  · have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht1) hv.1
    nlinarith [mul_nonneg ht hh.1]
  · have hm := mul_le_mul_of_nonneg_left hv.2 (show 0 ≤ t - 1 by linarith)
    have hc := mul_nonneg hh.1 (show 0 ≤ (18 : ℝ) / 100 - 103 * t / 1000 by linarith)
    nlinarith

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- A derivative-free version of the rearrangement estimate: the low-rank slope
bound and the endpoint drop control the entire interval integral. -/
theorem packingDelta_clipped_bound
    (hlow : ∀ a b, 0 ≤ a → a ≤ b → b ≤ lam → phi a - phi b ≤ b - a)
    {p q x : ℝ} (hp : p ∈ Ioo lam 1) (hx : x ∈ Ico (0 : ℝ) lam)
    (hq : 0 ≤ q) (hqx : q ≤ x) :
    let hh := 1 - p
    let v := x - q
    let w := v - (phi q - phi x)
    packingDelta phi p q ≤ hh * phi q -
      ((max (hh - w) 0) ^ 2 - (max (hh - v) 0) ^ 2) / 2 := by
  let hh := 1 - p
  let v := x - q
  let w := v - (phi q - phi x)
  have hh0 : 0 ≤ hh := by dsimp [hh]; linarith [hp.2]
  have hv : 0 ≤ v := sub_nonneg.mpr hqx
  have hq1 : q ≤ 1 := hqx.trans (hx.2.le.trans h.lam_lt_one.le)
  have hx1 : x ≤ 1 := hx.2.le.trans h.lam_lt_one.le
  have hdrop : 0 ≤ phi q - phi x := sub_nonneg.mpr
    (h.decreasing.antitoneOn ⟨hq, hq1⟩ ⟨hx.1, hx1⟩ hqx)
  have hw : w ∈ Icc (0 : ℝ) v := by
    have hlo := hlow q x hq hqx hx.2.le
    constructor <;> dsimp [w, v] <;> linarith
  have hqh : q + hh ≤ 1 := by dsimp [hh]; linarith [hp.1, hx.2]
  have hintphi := h.shift_integrable hq hh0 hqh
  have hintw : IntervalIntegrable (fun s : ℝ => max (s - w) 0) volume 0 hh :=
    (by fun_prop : Continuous (fun s : ℝ => max (s - w) 0)).intervalIntegrable 0 hh
  have hintv : IntervalIntegrable (fun s : ℝ => max (s - v) 0) volume 0 hh :=
    (by fun_prop : Continuous (fun s : ℝ => max (s - v) 0)).intervalIntegrable 0 hh
  have hpoint : ∀ s ∈ Icc (0 : ℝ) hh,
      phi (q + s) ≤ phi q - (max (s - w) 0 - max (s - v) 0) := by
    intro s hs
    have hqs : q + s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    by_cases hsw : s ≤ w
    · rw [max_eq_right (sub_nonpos.mpr hsw), max_eq_right (by linarith [hw.2])]
      simpa using h.decreasing.antitoneOn ⟨hq, hq1⟩ hqs (by linarith [hs.1])
    · rw [max_eq_left (by linarith)]
      by_cases hsv : s ≤ v
      · rw [max_eq_right (sub_nonpos.mpr hsv)]
        have hh := hlow (q + s) x hqs.1 (by dsimp [v] at hsv; linarith) hx.2.le
        dsimp [w, v]
        linarith
      · rw [max_eq_left (by linarith)]
        have hh := h.decreasing.antitoneOn ⟨hx.1, hx1⟩ hqs (by dsimp [v] at hsv; linarith)
        dsimp [w, v]
        linarith
  have hbound := intervalIntegral.integral_mono_on hh0 hintphi
    ((intervalIntegrable_const (c := phi q)).sub (hintw.sub hintv)) hpoint
  rw [h.shift_integral hq hh0 hqh,
    intervalIntegral.integral_sub (intervalIntegrable_const (c := phi q)) (hintw.sub hintv),
    intervalIntegral.integral_sub hintw hintv,
    integral_positive_ramp hw.1 hh0, integral_positive_ramp hv hh0,
    intervalIntegral.integral_const] at hbound
  change packingDelta phi p q ≤ _
  unfold packingDelta
  have heq : q + hh = 1 - p + q := by dsimp [hh]; ring
  rw [heq] at hbound
  simp only [sub_zero, smul_eq_mul] at hbound
  dsimp [w, v, hh] at *
  linarith

/-- Whenever the quantitative short-split condition holds, the clipped
correction preserves the low-rank verifier inequality. -/
theorem lowFirst_largeCorrection_short
    (hlow : ∀ a b, 0 ≤ a → a ≤ b → b ≤ lam → phi a - phi b ≤ b - a)
    {p q x beta : ℝ} (hp : p ∈ Ioo lam 1) (hx : x ∈ Ico (0 : ℝ) lam)
    (hq : 0 ≤ q) (hqx : q ≤ x) (hb : 0 ≤ beta)
    (htwo : beta * (1 - p) ≤ 2)
    (hshort : (beta * (1 - p) - 1) * (x - q) ≤ beta * (1 - p) * (1 - p) / 2)
    (hbinary : q + beta * packingDelta phi p q ≤ lam) :
    q + beta * packingDelta phi p q + largeMassCorrection phi lam p beta x ≤ lam := by
  by_cases hc : lam - x - beta * (1 - p) * phi x ≤ 0
  · simpa only [largeMassCorrection, max_eq_right hc, add_zero] using hbinary
  · have hdelta := h.packingDelta_clipped_bound hlow hp hx hq hqx
    dsimp only at hdelta
    have hscaled := mul_le_mul_of_nonneg_left hdelta hb
    have hw : x - q - (phi q - phi x) ∈ Icc (0 : ℝ) (x - q) := by
      have hlo := hlow q x hq hqx hx.2.le
      have hanti := h.decreasing.antitoneOn
        ⟨hq, hqx.trans (hx.2.le.trans h.lam_lt_one.le)⟩
        ⟨hx.1, hx.2.le.trans h.lam_lt_one.le⟩ hqx
      constructor <;> linarith
    have halg := clipped_rearrangement_nonpos (sub_pos.mpr hp.2).le (sub_nonneg.mpr hqx)
      hw hb (rfl : beta * (1 - p) = beta * (1 - p)) htwo hshort
    rw [largeMassCorrection, max_eq_left (le_of_not_ge hc)]
    nlinarith

theorem largeMassCorrection_eq_zero_of_ratio {p x beta : ℝ}
    (hx : x ∈ Ico (0 : ℝ) lam)
    (hr : lowRankRatio phi lam x ≤ beta * (1 - p)) :
    largeMassCorrection phi lam p beta x = 0 := by
  have hh := (div_le_iff₀ (h.positive hx)).mp hr
  exact max_eq_right (by linarith)

theorem largeMassCorrection_pos_before_line {p x beta r : ℝ}
    (hx : x ∈ Ico (0 : ℝ) lam)
    (hline : ∀ y ∈ Icc r lam, phi y = lam - y)
    (ht : 1 ≤ beta * (1 - p))
    (hc : 0 < largeMassCorrection phi lam p beta x) : x < r := by
  by_contra hn
  have hphi := hline x ⟨le_of_not_gt hn, hx.2.le⟩
  have hm := mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr hx.2.le)
  have hzero : largeMassCorrection phi lam p beta x = 0 := by
    unfold largeMassCorrection
    rw [hphi]
    apply max_eq_right
    linarith
  rw [hzero] at hc
  exact lt_irrefl _ hc

/-- The far-split interval check (C.26) is exactly the remaining clipped
correction inequality when the correction is positive. -/
theorem lowFirst_largeCorrection_far {p q x beta : ℝ} (hp : p < 1)
    (hc : 0 < largeMassCorrection phi lam p beta x)
    (hfar : q - x + beta * (1 - p) * (packingDelta phi p q / (1 - p) - phi x) ≤ 0) :
    q + beta * packingDelta phi p q + largeMassCorrection phi lam p beta x ≤ lam := by
  have hh : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  have hcraw : 0 ≤ lam - x - beta * (1 - p) * phi x := by
    have hraw : 0 < lam - x - beta * (1 - p) * phi x :=
      (lt_max_iff.mp hc).resolve_right (lt_irrefl _)
    exact hraw.le
  rw [largeMassCorrection, max_eq_left hcraw]
  have heq : beta * (1 - p) * (packingDelta phi p q / (1 - p) - phi x) =
      beta * packingDelta phi p q - beta * (1 - p) * phi x := by field_simp <;> ring
  rw [heq] at hfar
  linarith

end VerifierCurve
end OptimalG
