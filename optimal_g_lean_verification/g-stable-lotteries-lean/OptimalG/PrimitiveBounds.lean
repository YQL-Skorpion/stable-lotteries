import OptimalG.VerifierConditions

/-! Exact primitive and packing estimates used in Appendix C.1. -/
namespace OptimalG
open Set MeasureTheory

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem integral_subinterval {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable phi volume a b :=
  (h.continuous.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab

theorem primitive_difference {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    curvePrimitive phi b - curvePrimitive phi a = ∫ r in a..b, phi r := by
  have hh := intervalIntegral.integral_add_adjacent_intervals
    (h.integral_subinterval le_rfl ha (hab.trans hb)) (h.integral_subinterval ha hab hb)
  unfold curvePrimitive
  linarith

theorem primitive_increment_upper {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    curvePrimitive phi b - curvePrimitive phi a ≤ (b - a) * phi a := by
  rw [h.primitive_difference ha hab hb]
  have hh := intervalIntegral.integral_mono_on hab (h.integral_subinterval ha hab hb)
    (intervalIntegrable_const (c := phi a)) (fun r hr =>
      h.decreasing.antitoneOn ⟨ha, hab.trans hb⟩ ⟨ha.trans hr.1, hr.2.trans hb⟩ hr.1)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh

theorem primitive_increment_lower {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (b - a) * phi b ≤ curvePrimitive phi b - curvePrimitive phi a := by
  rw [h.primitive_difference ha hab hb]
  have hh := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := phi b))
    (h.integral_subinterval ha hab hb) (fun r hr =>
      h.decreasing.antitoneOn ⟨ha.trans hr.1, hr.2.trans hb⟩ ⟨ha.trans hab, hb⟩ hr.2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh

theorem primitive_above_tangent {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    q * phi q ≤ curvePrimitive phi q := by
  have hh := h.primitive_increment_lower (a := 0) le_rfl hq.1 hq.2
  simpa only [curvePrimitive, intervalIntegral.integral_same, sub_zero] using hh

/-- The chord inequality, derived directly from decreasing interval averages. -/
theorem primitive_chord_mul {p q : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) (hp : p ≤ 1) :
    q * curvePrimitive phi p ≤ p * curvePrimitive phi q := by
  have h1 := h.primitive_above_tangent ⟨hq, hqp.trans hp⟩
  have h2 := h.primitive_increment_upper hq hqp hp
  have hmul1 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hqp)
  have hmul2 := mul_le_mul_of_nonneg_left h2 hq
  nlinarith

theorem primitive_chord {p q : ℝ} (hp0 : 0 < p) (hq : 0 ≤ q) (hqp : q ≤ p) (hp : p ≤ 1) :
    (q / p) * curvePrimitive phi p ≤ curvePrimitive phi q := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hp0]
  nlinarith [h.primitive_chord_mul hq hqp hp]

theorem primitive_nonneg {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : 0 ≤ curvePrimitive phi q := by
  have hh := h.primitive_chord_mul hq.1 hq.2 (le_refl (1 : ℝ))
  simpa only [curvePrimitive, h.integral_zero, mul_zero, one_mul] using hh

/-- Strict decrease and zero total area make the primitive positive at every interior rank. -/
theorem primitive_pos {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) : 0 < curvePrimitive phi q := by
  by_cases hql : q ≤ lam
  · have hhalf : q / 2 ∈ Ico (0 : ℝ) lam := ⟨by linarith [hq.1], by linarith [hq.1]⟩
    have hp := h.positive hhalf
    have harea := h.primitive_above_tangent ⟨hhalf.1, hhalf.2.le.trans h.lam_lt_one.le⟩
    have hrest := h.primitive_increment_lower (a := q / 2) (b := q)
      hhalf.1 (by linarith [hq.1]) hq.2.le
    have hn := mul_nonneg (show 0 ≤ q - q / 2 by linarith [hq.1]) (h.nonnegative ⟨hq.1.le, hql⟩)
    have hh := mul_pos (show 0 < q / 2 by linarith [hq.1]) hp
    linarith
  · have hp := h.decreasing h.lam_mem ⟨hq.1.le, hq.2.le⟩ (lt_of_not_ge hql)
    rw [h.at_lam] at hp
    have hh := h.primitive_increment_upper (a := q) (b := 1) hq.1.le hq.2.le le_rfl
    have hz : curvePrimitive phi 1 = 0 := h.integral_zero
    rw [hz] at hh
    have hm := mul_neg_of_pos_of_neg (sub_pos.mpr hq.2) hp
    linarith

theorem primitive_le_tail {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : curvePrimitive phi q ≤ 1 - q := by
  have hh := h.primitive_increment_lower hq.1 hq.2 (le_refl (1 : ℝ))
  have hz : curvePrimitive phi 1 = 0 := h.integral_zero
  rw [hz, h.at_one] at hh
  linarith

theorem packingDelta_le_mass {p q : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hq : 0 ≤ q) (hqp : q ≤ p) :
    packingDelta phi p q ≤ p - q := by
  have htail := h.primitive_le_tail (q := 1 - p + q) ⟨by linarith [hp.2], by linarith⟩
  have hnonneg := h.primitive_nonneg ⟨hq, hqp.trans hp.2⟩
  unfold packingDelta
  linarith

theorem packingDelta_le_score {p q : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hq : 0 ≤ q) (hqp : q ≤ p) :
    packingDelta phi p q ≤ (1 - p) * phi q := by
  have hh := h.primitive_increment_upper (a := q) (b := 1 - p + q) hq
    (by linarith [hp.2]) (by linarith)
  unfold packingDelta
  convert hh using 1 <;> ring

theorem packingK_le_score {p q z : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) (hpz : p ≤ z) (hz : z ≤ 1) :
    packingK phi p q z ≤ -(p - q) * phi z - curvePrimitive phi q := by
  have hh := h.primitive_increment_lower (a := z - p + q) (b := z)
    (by linarith) (by linarith) hz
  unfold packingK
  nlinarith

theorem packingK_le_chord {p q z : ℝ} (hp0 : 0 < p) (hq : 0 ≤ q) (hqp : q ≤ p)
    (hpz : p ≤ z) (hz : z ≤ 1) :
    packingK phi p q z ≤ -(q / p) * curvePrimitive phi p - (p - q) * phi z := by
  have hh := h.packingK_le_score hq hqp hpz hz
  have hc := h.primitive_chord hp0 hq hqp (hpz.trans hz)
  linarith

/-- Moving a packed block right can only increase its centered score. -/
theorem packingK_monotone {p q : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) :
    MonotoneOn (packingK phi p q) (Icc p 1) := by
  intro y hy z hz hyz
  let d := p - q
  have hd : 0 ≤ d := sub_nonneg.mpr hqp
  have hint (r : ℝ) (hr : r ∈ Icc p 1) :
      IntervalIntegrable (fun u => phi (u + (r - d))) volume 0 d := by
    apply (h.continuous.comp (continuous_id.add_const (r - d)).continuousOn ?_).intervalIntegrable_of_Icc hd
    intro u hu
    constructor <;> dsimp [d] at * <;> linarith [hr.1, hr.2, hu.1, hu.2]
  have htrans (r : ℝ) (hr : r ∈ Icc p 1) :
      (∫ u in (0 : ℝ)..d, phi (u + (r - d))) = curvePrimitive phi r - curvePrimitive phi (r - p + q) := by
    rw [intervalIntegral.integral_comp_add_right]
    have heq : d + (r - d) = r := by ring
    rw [zero_add, heq]
    have heq2 : r - d = r - p + q := by dsimp [d]; ring
    rw [heq2, h.primitive_difference (by linarith [hr.1]) (by linarith) hr.2]
  have hh := intervalIntegral.integral_mono_on hd (hint z hz) (hint y hy) (by
    intro u hu
    apply h.decreasing.antitoneOn
    · constructor <;> dsimp [d] at * <;> linarith [hy.1, hy.2, hu.1, hu.2]
    · constructor <;> dsimp [d] at * <;> linarith [hz.1, hz.2, hu.1, hu.2]
    · linarith)
  rw [htrans z hz, htrans y hy] at hh
  unfold packingK
  linarith

end VerifierCurve
end OptimalG
