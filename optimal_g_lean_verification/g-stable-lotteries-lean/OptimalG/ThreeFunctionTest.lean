import OptimalG.PrimitiveBounds
import OptimalG.Algebra

/-! The three-function sufficient test of Appendix C.1, including the clipped correction. -/
namespace OptimalG
open Set

structure ThreeFunctionTest (phi : ℝ → ℝ) (lam p beta eta : ℝ) : Prop where
  beta_nonneg : 0 ≤ beta
  eta_nonneg : 0 ≤ eta
  first : ∀ x ∈ Icc (0 : ℝ) lam, ∀ q, 0 ≤ q → q ≤ p → q ≤ x →
    x + q - 2 * lam + beta * packingDelta phi p q + eta * phi x ≤ 0
  second : ∀ y ∈ Icc p lam, ∀ q, 0 ≤ q → q ≤ p →
    y + q - lam + beta * packingK phi p q y + eta * phi y ≤ 0
  third : ∀ z ∈ Icc lam 1, ∀ q, 0 ≤ q → q ≤ p →
    z + q - lam + beta * packingK phi p q z + eta * phi z ≤ 0

theorem threeFunctionTest_verifier {phi : ℝ → ℝ} {lam p beta eta : ℝ}
    (h : VerifierCurve phi lam) (hp0 : 0 < p) (hpl : p ≤ lam)
    (ht : ThreeFunctionTest phi lam p beta eta) :
    VerifierOn {p} phi lam (fun _ => beta) (fun _ x => correction lam eta x (phi x)) := by
  have hfirst0 (q : ℝ) (hq : 0 ≤ q) (hqp : q ≤ p) :
      q + beta * packingDelta phi p q ≤ lam := by
    have hh := ht.first lam ⟨h.lam_pos.le, le_rfl⟩ q hq hqp (hqp.trans hpl)
    rw [h.at_lam, mul_zero] at hh
    linarith
  have hsecond0 (q z : ℝ) (hq : 0 ≤ q) (hqp : q ≤ p) (hpz : p ≤ z) (hzl : z ≤ lam) :
      q + beta * packingK phi p q z ≤ 0 := by
    have hh := ht.second lam ⟨hpl, le_rfl⟩ q hq hqp
    rw [h.at_lam, mul_zero] at hh
    have hm := h.packingK_monotone hq hqp ⟨hpz, hzl.trans h.lam_lt_one.le⟩
      ⟨hpl, h.lam_lt_one.le⟩ hzl
    have hb := mul_le_mul_of_nonneg_left hm ht.beta_nonneg
    linarith
  constructor
  · intro r hr; exact ht.beta_nonneg
  · intro r hr x hx; exact correction_nonnegative lam eta x (phi x)
  · intro r hr x hx q hq hqr hqx
    have hrp : r = p := hr
    subst r
    have hh := ht.first x ⟨hx.1, hx.2.le⟩ q hq hqr hqx
    have hbase := hfirst0 q hq hqr
    unfold correction
    rcases le_total 0 (eta * phi x - (lam - x)) with hc | hc
    · rw [max_eq_left hc]; linarith
    · rw [max_eq_right hc]; linarith
  · intro r hr x hx q hq hqr hrx
    have hrp : r = p := hr
    subst r
    have hh := ht.second x ⟨hrx, hx.2.le⟩ q hq hqr
    have hbase := hsecond0 q x hq hqr hrx hx.2.le
    unfold correction
    rcases le_total 0 (eta * phi x - (lam - x)) with hc | hc
    · rw [max_eq_left hc]; linarith
    · rw [max_eq_right hc]; linarith
  · intro r hr x hx q hq hqr
    have hrp : r = p := hr
    subst r
    have hql : q ≤ lam := hqr.trans hpl
    rw [rankPotential_low phi lam x q hql,
      max_eq_right (neg_nonpos.mpr (h.nonnegative ⟨hq, hql⟩)), zero_mul, add_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (h.positive hx).le (by linarith [hfirst0 q hq hqr])
  · intro r hr x hx q z hq hqr hrz hz1
    have hrp : r = p := hr
    subst r
    have hql : q ≤ lam := hqr.trans hpl
    rw [rankPotential_low phi lam x q hql, add_zero]
    by_cases hzl : z ≤ lam
    · rw [rankPotential_low phi lam x z hzl,
        max_eq_right (neg_nonpos.mpr (h.nonnegative ⟨hp0.le.trans hrz, hzl⟩)), zero_mul, sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (h.positive hx).le (hsecond0 q z hq hqr hrz hzl)
    · have hzphi := h.nonpositive ⟨le_of_not_ge hzl, hz1⟩
      have hh := ht.third z ⟨le_of_not_ge hzl, hz1⟩ q hq hqr
      have hc : eta * phi x ≤ lam - x + correction lam eta x (phi x) := by
        have hc' := le_max_left (eta * phi x - (lam - x)) 0
        change _ ≤ correction lam eta x (phi x) at hc'
        linarith
      have hcphi := mul_le_mul_of_nonpos_right hc hzphi
      have hmain := mul_nonpos_of_nonneg_of_nonpos (h.positive hx).le hh
      have hcancel := div_mul_cancel₀ (lam - x) (ne_of_gt (h.positive hx))
      simp only [rankPotential, if_neg hzl, max_eq_left (neg_nonneg.mpr hzphi)]
      nlinarith

/-- The low second test can be checked at q=p when η≤1+βp. -/
theorem secondTest_of_endpoint {phi : ℝ → ℝ} {lam p beta eta : ℝ}
    (h : VerifierCurve phi lam) (hp0 : 0 < p) (hpl : p ≤ lam)
    (hb : 0 ≤ beta) (heta : eta ≤ 1 + beta * p)
    (hend : ∀ y ∈ Icc p lam, y + p - lam + eta * phi y - beta * curvePrimitive phi p ≤ 0) :
    ∀ y ∈ Icc p lam, ∀ q, 0 ≤ q → q ≤ p →
      y + q - lam + beta * packingK phi p q y + eta * phi y ≤ 0 := by
  intro y hy q hq hqp
  have hK := h.packingK_le_chord hp0 hq hqp hy.1 (hy.2.trans h.lam_lt_one.le)
  have hbK := mul_le_mul_of_nonneg_left hK hb
  have hphi := h.nonnegative ⟨hp0.le.trans hy.1, hy.2⟩
  have hcap := h.ceiling y ⟨hp0.le.trans hy.1, hy.2.trans h.lam_lt_one.le⟩
  have hA0 : y - lam + (eta - beta * p) * phi y ≤ 0 := by
    have hh := mul_le_mul_of_nonneg_right heta hphi
    nlinarith
  have hAp := hend y hy
  have ht0 : 0 ≤ q / p := div_nonneg hq hp0.le
  have ht1 : q / p ≤ 1 := (div_le_one hp0).mpr hqp
  have hmix := add_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) hA0)
    (mul_nonpos_of_nonneg_of_nonpos ht0 hAp)
  have hid : (1 - q / p) * (y - lam + (eta - beta * p) * phi y) +
      q / p * (y + p - lam + eta * phi y - beta * curvePrimitive phi p) =
      y + q - lam + beta * (-(q / p) * curvePrimitive phi p - (p - q) * phi y) + eta * phi y := by
    field_simp
    ring
  rw [hid] at hmix
  linarith

end OptimalG
