import OptimalG.PrimitiveBounds
import Mathlib.Analysis.Convex.Function

/-! Integral consequences of concavity, avoiding differentiation of the completed curve. -/
namespace OptimalG
open Set MeasureTheory

/-- Equal-length increments of a concave function decrease as the interval moves right. -/
theorem concave_increment_antitone {phi : ℝ → ℝ} {S : Set ℝ}
    (hc : ConcaveOn ℝ S phi) {x y d : ℝ} (hx : x ∈ S) (hyd : y + d ∈ S)
    (hxy : x ≤ y) (hd : 0 ≤ d) : phi (y + d) - phi y ≤ phi (x + d) - phi x := by
  by_cases heq : y + d - x = 0
  · have hyx : y = x := by linarith
    have hd0 : d = 0 := by linarith
    simp [hyx, hd0]
  · have hpos : 0 < y + d - x := lt_of_le_of_ne (by linarith) (Ne.symm heq)
    have ha : 0 ≤ (y - x) / (y + d - x) := div_nonneg (sub_nonneg.mpr hxy) hpos.le
    have hb : 0 ≤ d / (y + d - x) := div_nonneg hd hpos.le
    have hab : (y - x) / (y + d - x) + d / (y + d - x) = 1 := by field_simp; ring
    have h1 := hc.2 hx hyd ha hb hab
    have h2 := hc.2 hx hyd hb ha (by linarith)
    simp only [smul_eq_mul] at h1 h2
    have hxmid : (y - x) / (y + d - x) * x + d / (y + d - x) * (y + d) = x + d := by
      field_simp; ring
    have hymid : d / (y + d - x) * x + (y - x) / (y + d - x) * (y + d) = y := by
      field_simp; ring
    rw [hxmid] at h1
    rw [hymid] at h2
    have hsum : (y - x) / (y + d - x) * phi x + d / (y + d - x) * phi (y + d) +
        (d / (y + d - x) * phi x + (y - x) / (y + d - x) * phi (y + d)) = phi x + phi (y + d) := by
      field_simp; ring
    linarith

/-- Concavity and the rank ceiling supply the verifier's integrated slope hypothesis. -/
theorem high_fall_of_concave {phi : ℝ → ℝ} {lam : ℝ}
    (hl : 0 ≤ lam) (hl1 : lam ≤ 1) (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (hz : phi lam = 0) (hcap : ∀ r ∈ Icc (0 : ℝ) 1, phi r ≤ lam - r) :
    ∀ y z, lam ≤ y → y ≤ z → z ≤ 1 → phi z - phi y ≤ y - z := by
  intro y z hly hyz hz1
  have hi := concave_increment_antitone hc (x := lam) (y := y) (d := z - y)
    ⟨le_rfl, hl1⟩ ⟨by linarith, by linarith⟩ hly (sub_nonneg.mpr hyz)
  have heq : y + (z - y) = z := by ring
  rw [heq, hz, sub_zero] at hi
  have hh := hcap (lam + (z - y)) ⟨by linarith, by linarith⟩
  linarith

theorem verifierCurve_of_concave {phi : ℝ → ℝ} {lam : ℝ}
    (hl : 0 < lam) (hl1 : lam < 1) (hcont : ContinuousOn phi (Icc 0 1))
    (hanti : StrictAntiOn phi (Icc 0 1)) (hint : (∫ r in (0 : ℝ)..1, phi r) = 0)
    (hzero : phi lam = 0) (hone : phi 1 = -1)
    (hcap : ∀ r ∈ Icc (0 : ℝ) 1, phi r ≤ lam - r) (hc : ConcaveOn ℝ (Icc lam 1) phi) :
    VerifierCurve phi lam :=
  ⟨hl, hl1, hcont, hanti, hint, hzero, hone, hcap, high_fall_of_concave hl.le hl1.le hc hzero hcap⟩

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem shift_integrable {r d : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d) (hrd : r + d ≤ 1) :
    IntervalIntegrable (fun u => phi (r + u)) volume 0 d := by
  apply (h.continuous.comp (continuous_const.add continuous_id).continuousOn ?_).intervalIntegrable_of_Icc hd
  intro u hu
  change 0 ≤ r + u ∧ r + u ≤ 1
  constructor <;> linarith [hu.1, hu.2]

theorem shift_integral {r d : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d) (hrd : r + d ≤ 1) :
    (∫ u in (0 : ℝ)..d, phi (r + u)) = curvePrimitive phi (r + d) - curvePrimitive phi r := by
  have heq : (fun u => phi (r + u)) = fun u => phi (u + r) := by funext u; rw [add_comm]
  rw [heq, intervalIntegral.integral_comp_add_right, zero_add, add_comm d r]
  exact (h.primitive_difference hr (by linarith) hrd).symm

theorem primitive_increment_difference_le (hc : ConcaveOn ℝ (Icc lam 1) phi)
    {a b d : ℝ} (ha : lam ≤ a) (hab : a ≤ b) (hd : 0 ≤ d) (hbd : b + d ≤ 1) :
    curvePrimitive phi (b + d) - curvePrimitive phi b -
      (curvePrimitive phi (a + d) - curvePrimitive phi a) ≤ d * (phi b - phi a) := by
  have ha0 : 0 ≤ a := h.lam_pos.le.trans ha
  have hb0 : 0 ≤ b := ha0.trans hab
  have had : a + d ≤ 1 := by linarith
  have hint := (h.shift_integrable hb0 hd hbd).sub (h.shift_integrable ha0 hd had)
  have hh := intervalIntegral.integral_mono_on hd hint
    (intervalIntegrable_const (c := phi b - phi a)) (by
      intro u hu
      have hi := concave_increment_antitone hc ⟨ha, by linarith⟩
        ⟨by linarith [hu.1], by linarith [hu.2]⟩ hab hu.1
      linarith)
  rw [intervalIntegral.integral_sub (h.shift_integrable hb0 hd hbd) (h.shift_integrable ha0 hd had),
    h.shift_integral hb0 hd hbd, h.shift_integral ha0 hd had] at hh
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hh

theorem primitive_loss_difference_le (hc : ConcaveOn ℝ (Icc lam 1) phi)
    {a b d : ℝ} (ha : lam ≤ a) (hab : a ≤ b) (hd : 0 ≤ d) (hbd : b + d ≤ 1) :
    curvePrimitive phi (a + d) - curvePrimitive phi a -
      (curvePrimitive phi (b + d) - curvePrimitive phi b) ≤ d * (phi (a + d) - phi (b + d)) := by
  have ha0 : 0 ≤ a := h.lam_pos.le.trans ha
  have hb0 : 0 ≤ b := ha0.trans hab
  have had : a + d ≤ 1 := by linarith
  have hint := (h.shift_integrable ha0 hd had).sub (h.shift_integrable hb0 hd hbd)
  have hh := intervalIntegral.integral_mono_on hd hint
    (intervalIntegrable_const (c := phi (a + d) - phi (b + d))) (by
      intro u hu
      have hi := concave_increment_antitone hc (x := a + u) (y := a + d) (d := b - a)
        ⟨by linarith [hu.1], by linarith [hu.2]⟩ ⟨by linarith, by linarith⟩
        (by linarith [hu.2]) (sub_nonneg.mpr hab)
      have heq1 : a + d + (b - a) = b + d := by ring
      have heq2 : a + u + (b - a) = b + u := by ring
      rw [heq1, heq2] at hi
      linarith)
  rw [intervalIntegral.integral_sub (h.shift_integrable ha0 hd had) (h.shift_integrable hb0 hd hbd),
    h.shift_integral ha0 hd had, h.shift_integral hb0 hd hbd] at hh
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hh

end VerifierCurve

/-- The high-split reduction of Appendix C.5, proved with integral increments.
Only its already-checked boundary at q=λ remains as a hypothesis. -/
theorem highSplit_reduction {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (p q z beta r u : ℝ) (hlq : lam ≤ q) (hqp : q ≤ p) (hpz : p ≤ z) (hz : z ≤ 1)
    (hb : 0 ≤ beta) (hr : 1 ≤ r) (hu : 0 ≤ u) (hbJ : beta * curvePrimitive phi p = p)
    (hboundary : z + beta * packingK phi p lam z - r * (phi lam - phi z) + u * phi z ≤ 0) :
    z + beta * packingK phi p q z - r * (phi q - phi z) + u * phi z ≤ 0 := by
  let d := z - p
  have hd : 0 ≤ d := sub_nonneg.mpr hpz
  have hpd : p + d = z := by dsimp [d]; ring
  have hqd : q + d ≤ z := by dsimp [d]; linarith
  have hqphi := h.nonpositive ⟨hlq, (hqp.trans hpz).trans hz⟩
  have hzphi := h.nonpositive ⟨(hlq.trans hqp).trans hpz, hz⟩
  have hru := mul_nonpos_of_nonneg_of_nonpos hu hzphi
  rcases le_total (beta * d) r with hbr | hbr
  · have hi := h.primitive_loss_difference_le hc hlq hqp hd (by rw [hpd]; exact hz)
    rw [hpd] at hi
    have hm := mul_le_mul_of_nonneg_left hi hb
    have hdiff : 0 ≤ phi (q + d) - phi z := by
      exact sub_nonneg.mpr (h.decreasing.antitoneOn
        ⟨by linarith [h.lam_pos], hqd.trans hz⟩
        ⟨by linarith [h.lam_pos], hz⟩ hqd)
    have hprod := mul_le_mul_of_nonneg_right hbr hdiff
    have hfall := h.high_fall q (q + d) hlq (by linarith) (hqd.trans hz)
    have hr0 : 0 ≤ r := le_trans (by norm_num) hr
    have hfallmul := mul_le_mul_of_nonneg_left hfall hr0
    have hrd := mul_le_mul_of_nonneg_right hr hd
    have hqeq : z - p + q = q + d := by dsimp [d]; ring
    unfold packingK
    rw [hqeq]
    dsimp [d] at *
    nlinarith
  · have hi := h.primitive_increment_difference_le hc (a := lam) (b := q) (d := d)
      le_rfl hlq hd (hqd.trans hz)
    have hm := mul_le_mul_of_nonneg_left hi hb
    have hprod := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hbr) hqphi
    rw [h.at_lam] at hboundary
    have hqeq : z - p + q = q + d := by dsimp [d]; ring
    have hleq : z - p + lam = lam + d := by dsimp [d]; ring
    unfold packingK at *
    rw [hqeq]
    rw [hleq] at hboundary
    rw [h.at_lam] at hm
    nlinarith

end OptimalG
