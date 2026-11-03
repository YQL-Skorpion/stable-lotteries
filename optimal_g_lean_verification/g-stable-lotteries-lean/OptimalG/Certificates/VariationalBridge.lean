import OptimalG.Certificates.Compact
import OptimalG.Certificates.Transcendental
import OptimalG.Certificates.Control
import OptimalG.Certificates.ControlSlope
import OptimalG.VariationalBounds

/-!
# Linking numerical certificates to the actual variational definitions

This module derives the certified compact rectangle from `Admissible`, imports
the sharp determinant bound, and constructs a genuine low-rank feasible witness.
No ODE or terminal feasibility is assumed or concluded by the Slater witness.
-/

namespace OptimalG.Variational

open MeasureTheory Set

@[simp] theorem certificates_quadratic (L r : ℝ) :
    Certificates.quadratic L r = quadratic L r := rfl

@[simp] theorem certificates_cap (L S r : ℝ) :
    Certificates.cap L S r = cap L S r := rfl

theorem Admissible.slack_lower_exact {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) : Certificates.Compact.scalarLower ≤ d.S := by
  have hr : (307 : ℝ) / 1000 ∈ Icc ell tEnd := by norm_num [ell, tEnd]
  have hcap := (h.lowPrimitive_lower hr).trans (h.lowPrimitive_le_cap hr)
  have hlo := h.1.1
  have hhi := h.1.2
  norm_num [lambdaLo, lambdaHi] at hlo hhi
  norm_num [quadratic, cap] at hcap
  have hD : 0 < (693 : ℝ) / 1000 - lam := by linarith
  have hfac : 0 ≤ ((562330 : ℝ) / 1000000 - lam) *
      ((693 : ℝ) / 1000 * (lam + (562330 : ℝ) / 1000000 - (6535 : ℝ) / 10000) -
        Certificates.Compact.scalarLower) := by
    apply mul_nonneg (by linarith)
    norm_num [Certificates.Compact.scalarLower]
    linarith
  have hprod : Certificates.Compact.scalarLower * ((693 : ℝ) / 1000 - lam) ≤
      d.S * ((693 : ℝ) / 1000 - lam) := by
    norm_num [Certificates.Compact.scalarLower] at *
    nlinarith
  exact (mul_le_mul_iff_of_pos_right hD).mp hprod

theorem Admissible.compact_lambdaRange {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) : Certificates.Compact.LambdaRange lam := by
  have hl := h.1
  norm_num [Certificates.Compact.LambdaRange, lambdaLo, lambdaHi] at hl ⊢
  exact hl

theorem Admissible.compact_scalarRange {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) : Certificates.Compact.ScalarRange d.S := by
  refine ⟨h.slack_lower_exact, ?_⟩
  have hs := h.2.1
  have hhi := h.1.2
  unfold slackUpper at hs
  norm_num [Certificates.Compact.scalarUpper, lambdaHi] at hhi hs ⊢
  linarith

/-- The paper's sharp determinant margin follows from the actual low-rank constraints. -/
theorem Admissible.determinant_sharp {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {c : Control} (hc : c ∈ controlDomain) :
    0.0519 < controlDeterminant lam d c := by
  have hp : c.1 ∈ Icc (0.25 : ℝ) 0.36 := by
    have hp := hc.1
    norm_num [pLo, pHi] at hp ⊢
    exact hp
  have hx : c.2.1 ≤ 0.38 := by
    have hx := hc.2.1.2
    norm_num [xHi] at hx ⊢
    exact hx
  have hy : c.2.2 ≤ 0.38 := by
    have hy := hc.2.2.2
    norm_num [xHi] at hy ⊢
    exact hy
  have hpz : c.1 ∈ Icc pLo zStart := by
    refine ⟨hc.1.1, ?_⟩
    have hp' := hc.1.2
    norm_num [pHi, zStart] at hp' ⊢
    linarith
  have hb := Certificates.Compact.determinant_gt lam d.S c.1 c.2.1 c.2.2
    (primitive lam d c.1) h.compact_lambdaRange h.compact_scalarRange hp hx hy
    (h.primitive_lower hpz)
  simpa only [controlDeterminant, OptimalG.determinant, certificates_quadratic] using hb

noncomputable def slaterData (lam : ℝ) : LowRankData :=
  ⟨0.026, Certificates.Slater.score lam⟩

theorem lowPrimitive_slater (lam r : ℝ) :
    lowPrimitive lam (slaterData lam) r = Certificates.Slater.primitive lam r := by
  have h := Certificates.Slater.primitive_integral lam r
  change cap lam 0.026 ell + (∫ u in ell..r, Certificates.Slater.score lam u) = _
  norm_num [ell] at h ⊢
  simpa only [certificates_cap] using h

/-- The polynomial witness belongs to the genuine L∞ low-rank class K_λ. -/
theorem slater_admissible (lam : ℝ) (hlam : lam ∈ Icc lambdaLo lambdaHi) :
    Admissible lam (slaterData lam) := by
  have hL : lam ∈ Icc (0.562325 : ℝ) 0.562330 := by
    norm_num [lambdaLo, lambdaHi] at hlam ⊢
    exact hlam
  have hw := Certificates.Slater.strict_witness lam hL
  have hcont : Continuous (Certificates.Slater.score lam) := hw.2.2.1
  have hb : ∀ᵐ r ∂volume.restrict (Icc ell tEnd),
      0 ≤ Certificates.Slater.score lam r ∧ Certificates.Slater.score lam r ≤ lam - r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hr' : r ∈ Icc (0.28 : ℝ) 0.385 := by
      norm_num [ell, tEnd] at hr ⊢
      exact hr
    have hs := Certificates.Slater.score_bounds lam r hL hr'
    constructor <;> linarith [hs.1, hs.2]
  have hnorm : ∀ᵐ r ∂volume.restrict (Icc ell tEnd),
      ‖Certificates.Slater.score lam r‖ ≤ 1 := by
    filter_upwards [hb, ae_restrict_mem measurableSet_Icc] with r hs hr
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    have hr0 := hr.1
    norm_num [ell] at hr0
    linarith [hs.2, hL.2]
  refine ⟨hlam, ?_, ?_, hb, ?_, ?_⟩
  · change (0.026 : ℝ) ≤ slackUpper lam
    have hs := hw.2.1
    norm_num [slackUpper, lambdaHi] at hs ⊢
    linarith
  · exact memLp_top_of_bound hcont.aestronglyMeasurable 1 hnorm
  · rw [lowPrimitive_slater]
    change Certificates.Slater.primitive lam tEnd = quadratic lam tEnd - 0.026
    have he := Certificates.Slater.primitive_right lam
    norm_num [tEnd] at he ⊢
    simpa only [certificates_quadratic] using he
  · intro r hr
    rw [lowPrimitive_slater]
    have hr' : r ∈ Icc (0.28 : ℝ) 0.385 := by
      norm_num [ell, tEnd] at hr ⊢
      exact hr
    have hm := Certificates.Slater.primitive_cap_margin lam r hL hr'
    change Certificates.Slater.primitive lam r ≤ cap lam 0.026 r
    rw [certificates_cap] at hm
    have hu : 0 ≤ r - 0.28 := sub_nonneg.mpr hr'.1
    nlinarith

/-- The certificate control is definitionally the rational formula (4.2). -/
theorem controlH_eq_certified_value (lam : ℝ) (d : LowRankData) (z u : ℝ) (c : Control) :
    controlH lam d z u c = Certificates.Control.value (z - lam) (2 * lam - c.2.1)
      (c.1 + c.2.2 - lam) (primitive lam d c.1)
      (quadratic lam (1 - c.1) - d.S) (quadratic lam (z - c.1) - d.S - u)
      (d.phi c.2.1) (d.phi c.2.2) := rfl

/-- The high-rank state box gives the geometric K budget used in Appendix D. -/
theorem Admissible.control_K_bounds {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {p z u : ℝ}
    (hp : p ∈ Icc pLo pHi) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z - quadratic lam 1 ≤ u)
    (huHigh : u ≤ quadratic lam z - d.S) :
    0 ≤ quadratic lam (z - p) - d.S - u ∧
      quadratic lam (z - p) - d.S - u ≤ 0.111315 := by
  have hll := h.1.1
  have hlu := h.1.2
  have hpl := hp.1
  have hpu := hp.2
  have hzl := hz.1
  have hzu := hz.2
  norm_num [lambdaLo, lambdaHi, pLo, pHi, zStart, zEnd] at hll hlu hpl hpu hzl hzu
  have hs0 : 0 ≤ d.S := by linarith [h.slack_lower]
  have hU0 : 0 ≤ z - lam := by linarith
  have hUmax : z - lam ≤ 0.313 := by linarith
  have hfac : 0 ≤ z - lam - p / 2 := by linarith
  have hprod := mul_nonneg (show 0 ≤ p by linarith) hfac
  have hsq := sq_nonneg (p - (z - lam))
  have hUsq := mul_nonneg (sub_nonneg.mpr hUmax) (show 0 ≤ 0.313 + (z - lam) by linarith)
  unfold quadratic at huLow huHigh ⊢
  constructor <;> nlinarith

/-- Both score-coordinate coefficients are positive for an actual admissible
profile and a state between the root budget and the ceiling. -/
theorem Admissible.control_coefficients_positive {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {c : Control} (hc : c ∈ controlDomain) {z u : ℝ}
    (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z - quadratic lam 1 ≤ u)
    (huHigh : u ≤ quadratic lam z - d.S) :
    0.0145 < Certificates.Control.cx (z - lam) (c.1 + c.2.2 - lam)
      (primitive lam d c.1) (quadratic lam (z - c.1) - d.S - u) ∧
    0.024 < Certificates.Control.cy (z - lam) (2 * lam - c.2.1)
      (quadratic lam (1 - c.1) - d.S) (quadratic lam (z - c.1) - d.S - u) := by
  have hp : c.1 ∈ Icc (0.25 : ℝ) 0.36 := by
    have hp := hc.1
    norm_num [pLo, pHi] at hp ⊢
    exact hp
  have hx : c.2.1 ≤ 0.38 := by
    have hx := hc.2.1.2
    norm_num [xHi] at hx ⊢
    exact hx
  have hy : 0.285 ≤ c.2.2 := by
    have hy := (le_max_left xLo c.1).trans hc.2.2.1
    norm_num [xLo] at hy ⊢
    exact hy
  have hz' : z ∈ Icc (0.775 : ℝ) 0.875 := by
    norm_num [zStart, zEnd] at hz ⊢
    exact hz
  have hr := h.control_R_lower hc.1
  have hP := Certificates.Compact.complementary_primitive_floor lam d.S c.1
    h.compact_lambdaRange h.compact_scalarRange hp
  have hK := h.control_K_bounds hc.1 hz huLow huHigh
  apply Certificates.Control.coefficients_positive lam c.1 c.2.1 c.2.2 z
    (primitive lam d c.1) (quadratic lam (1 - c.1) - d.S)
    (quadratic lam (z - c.1) - d.S - u) h.compact_lambdaRange hp hx hy hz'
  · norm_num at hr ⊢
    exact hr
  · simpa only [certificates_quadratic] using le_of_lt hP
  · exact hK.1
  · exact hK.2

/-- The primitive cap on every rank used by a high-rank control. -/
theorem Admissible.control_primitive_cap {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {p : ℝ} (hp : p ∈ Icc pLo pHi) :
    primitive lam d p ≤ cap lam d.S p := by
  unfold primitive
  split_ifs with he ht
  · exact le_rfl
  · exact h.lowPrimitive_le_cap ⟨le_of_lt (lt_of_not_ge he), ht⟩
  · have := hp.2
    norm_num [pHi, tEnd] at this ht
    linarith

/-- Sharp coupled score-coefficient ratio, derived from the actual cap and
state ceiling rather than independent interval boxes for the primitive. -/
theorem Admissible.control_coefficient_ratio {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {c : Control} (hc : c ∈ controlDomain) {z u : ℝ}
    (hz : z ∈ Icc zStart zEnd) (hu : u ≤ quadratic lam z-d.S) :
    Certificates.Control.cx (z-lam) (c.1+c.2.2-lam) (primitive lam d c.1)
        (quadratic lam (z-c.1)-d.S-u) <
      0.74 * Certificates.Control.cy (z-lam) (2*lam-c.2.1)
        (quadratic lam (1-c.1)-d.S) (quadratic lam (z-c.1)-d.S-u) := by
  have hp : c.1 ∈ Icc (0.25:ℝ) 0.36 := by
    have hp := hc.1
    norm_num [pLo, pHi] at hp ⊢
    exact hp
  have hx : c.2.1 ≤ 0.38 := by
    have hx := hc.2.1.2
    norm_num [xHi] at hx ⊢
    exact hx
  have hy : c.2.2 ≤ 0.38 := by
    have hy := hc.2.2.2
    norm_num [xHi] at hy ⊢
    exact hy
  have hU : z-lam ∈ Icc (0.21267:ℝ) 0.313 := by
    have hzl := hz.1
    have hzu := hz.2
    have hl := h.1
    norm_num [zStart, zEnd, lambdaLo, lambdaHi] at hzl hzu hl
    constructor <;> linarith [hl.1, hl.2]
  have hcap := h.control_primitive_cap hc.1
  rw [← certificates_cap, Certificates.cap_eq_quotient _ _ _ (by linarith [hp.2])] at hcap
  have hr : (1-c.1)*primitive lam d c.1 ≤ lam*(Certificates.quadratic lam (1-c.1)-d.S) := by
    have hm := (le_div_iff₀ (show 0 < 1-c.1 by linarith [hp.2])).mp hcap
    nlinarith
  have hk : c.1*((z-lam)-c.1/2) ≤ quadratic lam (z-c.1)-d.S-u := by
    unfold quadratic at hu ⊢
    nlinarith
  simpa only [certificates_quadratic] using Certificates.Control.coefficient_ratio
    lam d.S c.1 (z-lam) c.2.1 c.2.2 (primitive lam d c.1)
    (quadratic lam (z-c.1)-d.S-u) h.compact_lambdaRange h.compact_scalarRange
    hp hU hx hy hr hk

/-- Uniform state-slope bound with pointwise score hypotheses; admissibility
supplies these hypotheses almost everywhere, which is handled separately. -/
theorem Admissible.control_alpha_lt {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {c : Control} (hc : c ∈ controlDomain)
    (hA0 : 0 ≤ d.phi c.2.1) (hA : d.phi c.2.1 ≤ lam-c.2.1)
    (hB0 : 0 ≤ d.phi c.2.2) (hB : d.phi c.2.2 ≤ lam-c.2.2) :
    Certificates.Control.alphaNumerator (2*lam-c.2.1) (c.1+c.2.2-lam)
      (d.phi c.2.1) (d.phi c.2.2) / controlDeterminant lam d c < 4.53 := by
  have hp : c.1 ∈ Icc (0.25:ℝ) 0.36 := by
    have hp := hc.1
    norm_num [pLo, pHi] at hp ⊢
    exact hp
  have hx : c.2.1 ∈ Icc (0.285:ℝ) 0.38 := by
    have hx := hc.2.1
    norm_num [xLo, xHi] at hx ⊢
    exact hx
  have hy : c.2.2 ∈ Icc (0.285:ℝ) 0.38 := by
    have hy0 := (le_max_left xLo c.1).trans hc.2.2.1
    have hy1 := hc.2.2.2
    norm_num [xLo, xHi] at hy0 hy1 ⊢
    exact ⟨hy0,hy1⟩
  exact Certificates.Control.alpha_lt lam c.1 c.2.1 c.2.2
    (primitive lam d c.1) (quadratic lam (1-c.1)-d.S) (d.phi c.2.1) (d.phi c.2.2)
    h.compact_lambdaRange hp hx hy ((le_max_right xLo c.1).trans hc.2.2.1)
    hA0 hA hB0 hB (h.determinant_sharp hc)

end OptimalG.Variational
