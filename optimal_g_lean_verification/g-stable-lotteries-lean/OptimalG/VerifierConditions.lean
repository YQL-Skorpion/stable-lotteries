import OptimalG.Potential
import OptimalG.RankPacking

/-! The exact functional inequalities supplied to the finite-election verifier.
These are hypotheses for the verifier lemma, not assertions of existence. -/
namespace OptimalG
open Set MeasureTheory

structure VerifierCurve (phi : ℝ → ℝ) (lam : ℝ) : Prop where
  lam_pos : 0 < lam
  lam_lt_one : lam < 1
  continuous : ContinuousOn phi (Icc 0 1)
  decreasing : StrictAntiOn phi (Icc 0 1)
  integral_zero : (∫ r in (0 : ℝ)..1, phi r) = 0
  at_lam : phi lam = 0
  at_one : phi 1 = -1
  ceiling : ∀ r ∈ Icc (0 : ℝ) 1, phi r ≤ lam - r
  high_fall : ∀ y z, lam ≤ y → y ≤ z → z ≤ 1 → phi z - phi y ≤ y - z

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem lam_mem : lam ∈ Icc (0 : ℝ) 1 := ⟨h.lam_pos.le, h.lam_lt_one.le⟩
theorem positive {x : ℝ} (hx : x ∈ Ico (0 : ℝ) lam) : 0 < phi x := by
  rw [← h.at_lam]
  exact h.decreasing ⟨hx.1, hx.2.le.trans h.lam_lt_one.le⟩ h.lam_mem hx.2

theorem nonpositive {x : ℝ} (hx : x ∈ Icc lam 1) : phi x ≤ 0 := by
  rw [← h.at_lam]
  exact h.decreasing.antitoneOn h.lam_mem ⟨h.lam_pos.le.trans hx.1, hx.2⟩ hx.1

theorem nonnegative {x : ℝ} (hx : x ∈ Icc (0 : ℝ) lam) : 0 ≤ phi x := by
  rw [← h.at_lam]
  exact h.decreasing.antitoneOn ⟨hx.1, hx.2.trans h.lam_lt_one.le⟩ h.lam_mem hx.2

theorem potential_nonneg {x z : ℝ} (hx : x ∈ Ico (0 : ℝ) lam)
    (hz : z ∈ Icc (0 : ℝ) 1) : 0 ≤ rankPotential phi lam x z := by
  apply rankPotential_nonneg phi lam x z (h.positive hx)
    (h.ceiling x ⟨hx.1, hx.2.le.trans h.lam_lt_one.le⟩)
  intro _
  exact h.ceiling z hz

theorem potential_monotone {x : ℝ} (hx : x ∈ Ico (0 : ℝ) lam) :
    MonotoneOn (rankPotential phi lam x) (Icc 0 1) :=
  rankPotential_monotoneOn phi lam x (h.positive hx)
    (h.ceiling x ⟨hx.1, hx.2.le.trans h.lam_lt_one.le⟩) h.at_lam h.high_fall

theorem negative_part_le {q s : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc lam 1) (hqs : q ≤ s) : max (-phi q) 0 ≤ -phi s := by
  apply max_le
  · exact neg_le_neg (h.decreasing.antitoneOn hq ⟨h.lam_pos.le.trans hs.1, hs.2⟩ hqs)
  · exact neg_nonneg.mpr (h.nonpositive hs)

end VerifierCurve

noncomputable def packingDelta (phi : ℝ → ℝ) (p q : ℝ) : ℝ :=
  curvePrimitive phi (1 - p + q) - curvePrimitive phi q
noncomputable def packingK (phi : ℝ → ℝ) (p q z : ℝ) : ℝ :=
  curvePrimitive phi (z - p + q) - curvePrimitive phi z - curvePrimitive phi q

/-- Equations 5.9--5.12, on a specified mass domain. -/
structure VerifierOn (masses : Set ℝ) (phi : ℝ → ℝ) (lam : ℝ)
    (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ) : Prop where
  beta_nonneg : ∀ p ∈ masses, 0 ≤ beta p
  corr_nonneg : ∀ p ∈ masses, ∀ x ∈ Ico (0 : ℝ) lam, 0 ≤ corr p x
  low_first : ∀ p ∈ masses, ∀ x ∈ Ico (0 : ℝ) lam, ∀ q,
    0 ≤ q → q ≤ p → q ≤ x → q + beta p * packingDelta phi p q + corr p x ≤ lam
  low_second : ∀ p ∈ masses, ∀ x ∈ Ico (0 : ℝ) lam, ∀ q,
    0 ≤ q → q ≤ p → p ≤ x → q + beta p * packingK phi p q x + corr p x ≤ 0
  high_first : ∀ p ∈ masses, ∀ x ∈ Ico (0 : ℝ) lam, ∀ q,
    0 ≤ q → q ≤ p → phi x * (q + beta p * packingDelta phi p q + rankPotential phi lam x q - lam)
      ≤ max (-phi q) 0 * corr p x
  high_second : ∀ p ∈ masses, ∀ x ∈ Ico (0 : ℝ) lam, ∀ q z,
    0 ≤ q → q ≤ p → p ≤ z → z ≤ 1 →
    phi x * (q + beta p * packingK phi p q z + rankPotential phi lam x q - rankPotential phi lam x z)
      ≤ max (-phi z) 0 * corr p x

theorem VerifierOn.transport {M N : Set ℝ} {phi : ℝ → ℝ} {lam : ℝ}
    {beta beta' : ℝ → ℝ} {corr corr' : ℝ → ℝ → ℝ}
    (hv : VerifierOn M phi lam beta corr) (hsub : N ⊆ M)
    (hb : ∀ p ∈ N, beta' p = beta p)
    (hc : ∀ p ∈ N, ∀ x ∈ Ico (0 : ℝ) lam, corr' p x = corr p x) :
    VerifierOn N phi lam beta' corr' := by
  constructor
  · intro p hp; rw [hb p hp]; exact hv.beta_nonneg p (hsub hp)
  · intro p hp x hx; rw [hc p hp x hx]; exact hv.corr_nonneg p (hsub hp) x hx
  · intro p hp x hx q hq hqp hqx; rw [hb p hp, hc p hp x hx]
    exact hv.low_first p (hsub hp) x hx q hq hqp hqx
  · intro p hp x hx q hq hqp hpx; rw [hb p hp, hc p hp x hx]
    exact hv.low_second p (hsub hp) x hx q hq hqp hpx
  · intro p hp x hx q hq hqp; rw [hb p hp, hc p hp x hx]
    exact hv.high_first p (hsub hp) x hx q hq hqp
  · intro p hp x hx q z hq hqp hpz hz; rw [hb p hp, hc p hp x hx]
    exact hv.high_second p (hsub hp) x hx q z hq hqp hpz hz

/-- At mass zero all coefficients can vanish. -/
theorem verifier_zero_mass {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam) :
    VerifierOn {0} phi lam (fun _ => 0) (fun _ _ => 0) := by
  constructor
  · simp
  · simp
  · intro p hp x hx q hq hqp hqx
    have hp0 : p = 0 := hp
    have hq0 : q = 0 := by linarith
    simp [hq0, h.lam_pos.le]
  · intro p hp x hx q hq hqp hpx
    have hp0 : p = 0 := hp
    have hq0 : q = 0 := by linarith
    simp [hq0]
  · intro p hp x hx q hq hqp
    have hp0 : p = 0 := hp
    have hq0 : q = 0 := by linarith
    simp only [hq0, zero_mul, add_zero, mul_zero]
    rw [rankPotential_low phi lam x 0 h.lam_pos.le]
    exact mul_nonpos_of_nonneg_of_nonpos (h.positive hx).le (by linarith [h.lam_pos])
  · intro p hp x hx q z hq hqp hpz hz
    have hp0 : p = 0 := hp
    have hq0 : q = 0 := by linarith
    simp only [hq0, zero_mul, add_zero, mul_zero]
    rw [rankPotential_low phi lam x 0 h.lam_pos.le]
    exact mul_nonpos_of_nonneg_of_nonpos (h.positive hx).le
      (by linarith [h.potential_nonneg hx ⟨by linarith, hz⟩])

/-- The mass-one coefficients cover zero-mass reference candidates at interior ranks. -/
theorem verifier_one_mass {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam) :
    VerifierOn {1} phi lam (fun _ => 0) (fun _ x => lam - x) := by
  have hfirst (x q : ℝ) (hx : x ∈ Ico (0 : ℝ) lam) (hq : q ∈ Icc (0 : ℝ) 1) :
      phi x * (q + rankPotential phi lam x q - lam) ≤ max (-phi q) 0 * (lam - x) := by
    by_cases hql : q ≤ lam
    · rw [rankPotential_low phi lam x q hql]
      have hpos := h.positive hx
      have hnonneg := h.nonnegative ⟨hq.1, hql⟩
      rw [max_eq_right (neg_nonpos.mpr hnonneg), zero_mul]
      exact mul_nonpos_of_nonneg_of_nonpos hpos.le (by linarith)
    · rw [rankPotential_mass_one phi lam x q (h.positive hx) h.at_lam (le_of_not_ge hql)]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sub_nonneg.mpr hx.2.le)
  constructor
  · simp
  · intro p hp x hx; exact sub_nonneg.mpr hx.2.le
  · intro p hp x hx q hq hqp hqx
    simp only [zero_mul, add_zero]
    linarith
  · intro p hp x hx q hq hqp hpx
    have hp1 : p = 1 := hp
    exfalso; linarith [hx.2, h.lam_lt_one]
  · intro p hp x hx q hq hqp
    have hp1 : p = 1 := hp
    simpa only [zero_mul, add_zero] using hfirst x q hx ⟨hq, by linarith⟩
  · intro p hp x hx q z hq hqp hpz hz
    have hp1 : p = 1 := hp
    have hz1 : z = 1 := by linarith
    subst z
    simp only [zero_mul, add_zero, h.at_one, neg_neg, max_eq_left (by norm_num : (0 : ℝ) ≤ 1), one_mul]
    have hq1 : q ≤ 1 := by linarith
    have hpot1 : lam ≤ rankPotential phi lam x 1 := by
      have hr := potential_ratio_ge_one phi lam x (h.positive hx)
        (h.ceiling x ⟨hx.1, hx.2.le.trans h.lam_lt_one.le⟩)
      simp only [rankPotential, if_neg (not_le.mpr h.lam_lt_one), h.at_one, mul_neg_one]
      linarith
    have hneg := h.negative_part_le ⟨hq, hq1⟩ ⟨h.lam_lt_one.le, le_rfl⟩ hq1
    rw [h.at_one, neg_neg] at hneg
    have hc : 0 ≤ lam - x := by linarith [hx.2]
    have hbound := hfirst x q hx ⟨hq, hq1⟩
    have hmul := mul_le_mul_of_nonneg_right hneg hc
    have hpot := mul_nonneg (h.positive hx).le (sub_nonneg.mpr hpot1)
    nlinarith

/-- Canonical endpoint extension of any verifier supplied for open masses. -/
theorem verifier_extend_endpoints {phi : ℝ → ℝ} {lam : ℝ}
    (h : VerifierCurve phi lam) (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Ioo 0 1) phi lam beta corr) :
    ∃ b c, VerifierOn (Icc 0 1) phi lam b c := by
  let b : ℝ → ℝ := fun p => if p = 0 ∨ p = 1 then 0 else beta p
  let c : ℝ → ℝ → ℝ := fun p x => if p = 0 then 0 else if p = 1 then lam - x else corr p x
  have hlocal (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
      VerifierOn {p} phi lam b c := by
    by_cases hp0 : p = 0
    · subst p
      apply (verifier_zero_mass h).transport (fun _ hr => hr)
      · intro r hr; have hr0 : r = 0 := hr; subst r; simp [b]
      · intro r hr x hx; have hr0 : r = 0 := hr; subst r; simp [c]
    · by_cases hp1 : p = 1
      · subst p
        apply (verifier_one_mass h).transport (fun _ hr => hr)
        · intro r hr; have hr1 : r = 1 := hr; subst r; simp [b]
        · intro r hr x hx; have hr1 : r = 1 := hr; subst r; simp [c]
      · have hpo : p ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), lt_of_le_of_ne hp.2 hp1⟩
        apply hv.transport (fun r hr => by have hrp : r = p := hr; simpa only [hrp] using hpo)
        · intro r hr; have hrp : r = p := hr; subst r; simp [b, hp0, hp1]
        · intro r hr x hx; have hrp : r = p := hr; subst r; simp [c, hp0, hp1]
  refine ⟨b, c, ?_⟩
  constructor
  · intro p hp; exact (hlocal p hp).beta_nonneg p rfl
  · intro p hp; exact (hlocal p hp).corr_nonneg p rfl
  · intro p hp; exact (hlocal p hp).low_first p rfl
  · intro p hp; exact (hlocal p hp).low_second p rfl
  · intro p hp; exact (hlocal p hp).high_first p rfl
  · intro p hp; exact (hlocal p hp).high_second p rfl

end OptimalG
