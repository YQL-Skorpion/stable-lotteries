import OptimalG.ConcaveIncrements
import OptimalG.ThreeFunctionTest

/-! Uniform split-rank reductions for Appendix C.4. -/
namespace OptimalG
open Set MeasureTheory

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- The score's low-rank slope bound controls the increase caused by an initial block. -/
theorem packingK_split_bound
    (hlow : ∀ u ∈ Icc (0 : ℝ) lam, phi 0 - u ≤ phi u)
    {p q z : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) (hql : q ≤ lam) (hpz : p ≤ z) (hz : z ≤ 1) :
    packingK phi p q z - packingK phi p 0 z ≤ q * (lam - z + p - phi 0) := by
  have hsint := h.shift_integrable (sub_nonneg.mpr hpz) hq (by linarith)
  have hqint := h.integral_subinterval le_rfl hq (hql.trans h.lam_lt_one.le)
  have hh := intervalIntegral.integral_mono_on hq (hsint.sub hqint)
    (intervalIntegrable_const (c := lam - z + p - phi 0)) (by
      intro u hu
      have hh := h.ceiling (z - p + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hl := hlow u ⟨hu.1, hu.2.trans hql⟩
      linarith)
  have heq : (∫ u in (0 : ℝ)..q, phi (z - p + u) - phi u) =
      packingK phi p q z - packingK phi p 0 z := by
    rw [intervalIntegral.integral_sub hsint hqint,
      h.shift_integral (sub_nonneg.mpr hpz) hq (by linarith)]
    simp only [packingK, curvePrimitive, intervalIntegral.integral_same, add_zero, sub_zero]
    ring
  rw [heq] at hh
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hh

theorem testValue_le_zero_split
    (hlow : ∀ u ∈ Icc (0 : ℝ) lam, phi 0 - u ≤ phi u)
    {p q z beta : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) (hql : q ≤ lam) (hpz : p ≤ z) (hz : z ≤ 1)
    (hb : 0 ≤ beta) (hgap : 1 ≤ beta * (phi 0 - lam + z - p)) :
    q + beta * packingK phi p q z ≤ beta * packingK phi p 0 z := by
  have hh := mul_le_mul_of_nonneg_left (h.packingK_split_bound hlow hq hqp hql hpz hz) hb
  have hg := mul_le_mul_of_nonneg_left hgap hq
  nlinarith

theorem firstTest_of_support
    (hlow : ∀ u ∈ Icc (0 : ℝ) lam, phi 0 - u ≤ phi u)
    {p beta eta : ℝ} (hp : p ∈ Icc (0 : ℝ) lam) (hb : 0 ≤ beta)
    (hgap : 1 ≤ beta * (phi 0 - lam + 1 - p))
    (hsupport : ∀ x ∈ Icc (0 : ℝ) lam,
      x + eta * phi x ≤ 2 * lam - beta * curvePrimitive phi (1 - p)) :
    ∀ x ∈ Icc (0 : ℝ) lam, ∀ q, 0 ≤ q → q ≤ p → q ≤ x →
      x + q - 2 * lam + beta * packingDelta phi p q + eta * phi x ≤ 0 := by
  intro x hx q hq hqp hqx
  have hh := h.testValue_le_zero_split hlow hq hqp (hqp.trans hp.2)
    (hp.2.trans h.lam_lt_one.le) (le_refl (1 : ℝ)) hb hgap
  have hz : curvePrimitive phi 1 = 0 := h.integral_zero
  have hzz : curvePrimitive phi 0 = 0 := by simp [curvePrimitive]
  simp only [packingK, packingDelta, hz, hzz, add_zero, sub_zero] at hh ⊢
  have hs := hsupport x hx
  linarith

theorem thirdTest_of_zero_split
    (hlow : ∀ u ∈ Icc (0 : ℝ) lam, phi 0 - u ≤ phi u)
    {p beta eta z0 : ℝ} (hp : p ∈ Icc (0 : ℝ) lam) (hz0 : lam ≤ z0) (hb : 0 ≤ beta)
    (hgap : 1 ≤ beta * (phi 0 - lam + z0 - p))
    (hbase : ∀ z ∈ Icc z0 1, z - lam + beta * packingK phi p 0 z + eta * phi z ≤ 0) :
    ∀ z ∈ Icc z0 1, ∀ q, 0 ≤ q → q ≤ p →
      z + q - lam + beta * packingK phi p q z + eta * phi z ≤ 0 := by
  intro z hz q hq hqp
  have hgp : 1 ≤ beta * (phi 0 - lam + z - p) :=
    hgap.trans (mul_le_mul_of_nonneg_left (by linarith [hz.1]) hb)
  have hh := h.testValue_le_zero_split hlow hq hqp (hqp.trans hp.2)
    ((hp.2.trans hz0).trans hz.1) hz.2 hb hgp
  have hs := hbase z hz
  linarith

/-- Small-mass high-rank test when η=1+βp. -/
theorem thirdTest_small_mass {p beta : ℝ} (hp0 : 0 < p) (hpl : p ≤ lam)
    (hb : 0 ≤ beta) (hbJ : p ≤ beta * curvePrimitive phi p) :
    ∀ z ∈ Icc lam 1, ∀ q, 0 ≤ q → q ≤ p →
      z + q - lam + beta * packingK phi p q z + (1 + beta * p) * phi z ≤ 0 := by
  intro z hz q hq hqp
  have hK := mul_le_mul_of_nonneg_left
    (h.packingK_le_chord hp0 hq hqp (hpl.trans hz.1) hz.2) hb
  have hbq : q ≤ beta * (q / p) * curvePrimitive phi p := by
    calc
      q = (q / p) * p := (div_mul_cancel₀ q (ne_of_gt hp0)).symm
      _ ≤ (q / p) * (beta * curvePrimitive phi p) :=
        mul_le_mul_of_nonneg_left hbJ (div_nonneg hq hp0.le)
      _ = _ := by ring
  have hcap := h.ceiling z ⟨h.lam_pos.le.trans hz.1, hz.2⟩
  have hnegative := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hb hq) (h.nonpositive hz)
  nlinarith

end VerifierCurve
end OptimalG
