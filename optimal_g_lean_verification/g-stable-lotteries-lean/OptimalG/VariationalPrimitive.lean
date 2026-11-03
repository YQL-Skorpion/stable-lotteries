import OptimalG.VariationalDefs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Consequences of the low-rank variational constraints -/

namespace OptimalG.Variational

open Set MeasureTheory

theorem Admissible.integrableOn {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) : IntegrableOn d.phi (Icc ell tEnd) := by
  exact MemLp.integrable (by simp) h.2.2.1

theorem Admissible.intervalIntegrable {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {a b : ℝ}
    (ha : ell ≤ a) (hab : a ≤ b) (hb : b ≤ tEnd) :
    IntervalIntegrable d.phi volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  apply h.integrableOn.mono_set
  intro r hr
  exact ⟨ha.trans hr.1, hr.2.trans hb⟩

theorem integral_line (lam a b : ℝ) :
    (∫ r in a..b, lam - r) = quadratic lam b - quadratic lam a := by
  have hc : IntervalIntegrable (fun _ : ℝ => lam) volume a b := intervalIntegrable_const
  have hi : IntervalIntegrable (fun r : ℝ => r) volume a b :=
    continuous_id.intervalIntegrable a b
  rw [intervalIntegral.integral_sub hc hi]
  rw [intervalIntegral.integral_const, integral_id]
  simp only [smul_eq_mul]
  unfold quadratic
  ring

/-- Before the fixed right endpoint, the primitive lies above Q_lambda-S.
This uses only almost-everywhere derivative bounds, as required before B.3. -/
theorem Admissible.lowPrimitive_lower {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {r : ℝ} (hr : r ∈ Icc ell tEnd) :
    quadratic lam r - d.S ≤ lowPrimitive lam d r := by
  have hleft := h.intervalIntegrable (le_refl ell) hr.1 hr.2
  have hright := h.intervalIntegrable hr.1 hr.2 (le_refl tEnd)
  have hbounds : ∀ᵐ u ∂volume.restrict (Icc r tEnd), d.phi u ≤ lam - u := by
    apply ae_restrict_of_ae_restrict_of_subset ?_ (h.2.2.2.1.mono (fun _ hu => hu.2))
    intro u hu
    exact ⟨hr.1.trans hu.1, hu.2⟩
  have hline : IntervalIntegrable (fun u : ℝ => lam - u) volume r tEnd :=
    (continuous_const.sub continuous_id).intervalIntegrable r tEnd
  have hint := intervalIntegral.integral_mono_ae_restrict hr.2 hright hline hbounds
  rw [integral_line] at hint
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hend := h.2.2.2.2.1
  dsimp [lowPrimitive] at hend ⊢
  linarith

theorem Admissible.lowPrimitive_le_cap {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {r : ℝ} (hr : r ∈ Icc ell tEnd) :
    lowPrimitive lam d r ≤ cap lam d.S r := h.2.2.2.2.2 r hr

/-- The scalar lower bound on S is forced by just one cap test at r=.307.
The weaker rounded bound .021972 is sufficient for the analytic domain bounds. -/
theorem Admissible.slack_lower {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) : (21972 : ℝ) / 1000000 ≤ d.S := by
  have hr : (307 : ℝ) / 1000 ∈ Icc ell tEnd := by norm_num [ell, tEnd]
  have hcap := (h.lowPrimitive_lower hr).trans (h.lowPrimitive_le_cap hr)
  have hlo := h.1.1
  have hhi := h.1.2
  norm_num [lambdaLo, lambdaHi] at hlo hhi
  norm_num [quadratic, cap] at hcap
  have hD : 0 < (693 : ℝ) / 1000 - lam := by linarith
  have hfac : 0 ≤ ((562330 : ℝ) / 1000000 - lam) *
      (lam + (562330 : ℝ) / 1000000 - (6535 : ℝ) / 10000) :=
    mul_nonneg (by linarith) (by linarith)
  have hprod : (21972 : ℝ) / 1000000 * ((693 : ℝ) / 1000 - lam) ≤
      d.S * ((693 : ℝ) / 1000 - lam) := by
    nlinarith
  exact (mul_le_mul_iff_of_pos_right hD).mp hprod

theorem Admissible.slack_upper {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) : d.S ≤ (26651 : ℝ) / 1000000 := by
  have hS := h.2.1
  have hhi := h.1.2
  unfold slackUpper at hS
  linarith

end OptimalG.Variational
