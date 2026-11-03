import OptimalG.VariationalBounds
import OptimalG.VariationalDomain
import OptimalG.VariationalEnvelope

/-! # The actual rational control family is uniformly Lipschitz in the state -/

namespace OptimalG.Variational

open Set MeasureTheory
open scoped NNReal

noncomputable def controlAlpha (lam : ℝ) (d : LowRankData) (c : Control) : ℝ :=
  ((c.1 + c.2.2 - lam) * d.phi c.2.1 +
    (2 * lam - c.2.1) * d.phi c.2.2) / controlDeterminant lam d c

theorem controlH_affine (lam : ℝ) (d : LowRankData) (z u : ℝ) (c : Control) :
    controlH lam d z u c = controlAlpha lam d c * u + controlH lam d z 0 c := by
  unfold controlH controlAlpha
  ring

theorem Admissible.control_phi_bounds {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) :
    ∀ᵐ c ∂controlMeasure,
      (0 ≤ d.phi c.2.1 ∧ d.phi c.2.1 ≤ (278 : ℝ) / 1000) ∧
      (0 ≤ d.phi c.2.2 ∧ d.phi c.2.2 ≤ (278 : ℝ) / 1000) := by
  have hphi := ae_control_lowRanks _ h.2.2.2.1
  have hmem : ∀ᵐ c ∂controlMeasure, c ∈ controlDomain :=
    ae_restrict_mem controlDomain_measurable
  filter_upwards [hphi, hmem] with c hpc hc
  have hhi := h.1.2
  have hx := hc.2.1.1
  have hy := (le_max_left xLo c.1).trans hc.2.2.1
  norm_num [lambdaHi, xLo] at hhi hx hy
  exact ⟨⟨hpc.1.1, by linarith [hpc.1.2]⟩,
    ⟨hpc.2.1, by linarith [hpc.2.2]⟩⟩

/-- A coarse bound of 9.5 already suffices for an existence theorem on the
entire interval of length .1. It is derived here, not assumed as a certificate. -/
theorem Admissible.controlAlpha_bound {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) :
    ∀ᵐ c ∂controlMeasure, |controlAlpha lam d c| ≤ (19 : ℝ) / 2 := by
  have hmem : ∀ᵐ c ∂controlMeasure, c ∈ controlDomain :=
    ae_restrict_mem controlDomain_measurable
  filter_upwards [h.control_phi_bounds, hmem] with c hphi hc
  have hdet := h.determinant_positive hc
  have hlo := h.1.1
  have hhi := h.1.2
  have hp := hc.1
  have hx := hc.2.1
  have hylo := (le_max_left xLo c.1).trans hc.2.2.1
  have hyhi := hc.2.2.2
  norm_num [lambdaLo, lambdaHi, pLo, pHi, xLo, xHi] at hlo hhi hp hx hylo hyhi
  have hk : |c.1 + c.2.2 - lam| ≤ (178 : ℝ) / 1000 := by
    apply abs_le.mpr
    constructor <;> linarith [hp.1, hp.2]
  have hh : |2 * lam - c.2.1| ≤ (84 : ℝ) / 100 := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2]
  have hfx : |d.phi c.2.1| ≤ (278 : ℝ) / 1000 := by
    rw [abs_of_nonneg hphi.1.1]
    exact hphi.1.2
  have hfy : |d.phi c.2.2| ≤ (278 : ℝ) / 1000 := by
    rw [abs_of_nonneg hphi.2.1]
    exact hphi.2.2
  have hnum : |(c.1 + c.2.2 - lam) * d.phi c.2.1 +
      (2 * lam - c.2.1) * d.phi c.2.2| ≤ (283004 : ℝ) / 1000000 := by
    calc
      _ ≤ |(c.1 + c.2.2 - lam) * d.phi c.2.1| +
        |(2 * lam - c.2.1) * d.phi c.2.2| := abs_add_le _ _
      _ = |c.1 + c.2.2 - lam| * |d.phi c.2.1| +
        |2 * lam - c.2.1| * |d.phi c.2.2| := by simp only [abs_mul]
      _ ≤ (178 : ℝ) / 1000 * ((278 : ℝ) / 1000) +
        (84 : ℝ) / 100 * ((278 : ℝ) / 1000) := by
          exact add_le_add (mul_le_mul hk hfx (abs_nonneg _) (by norm_num))
            (mul_le_mul hh hfy (abs_nonneg _) (by norm_num))
      _ = _ := by norm_num
  unfold controlAlpha
  rw [abs_div, abs_of_pos (show 0 < controlDeterminant lam d c by linarith)]
  apply (div_le_iff₀ (show 0 < controlDeterminant lam d c by linarith)).mpr
  nlinarith

noncomputable def controlBeta (lam : ℝ) (d : LowRankData) (c : Control) : ℝ :=
  (primitive lam d c.1 * d.phi c.2.1 +
    (quadratic lam (1 - c.1) - d.S) * d.phi c.2.2) /
      controlDeterminant lam d c

theorem controlH_quadratic (lam : ℝ) (d : LowRankData) (z u : ℝ) (c : Control) :
    controlH lam d z u c = (controlAlpha lam d c / 2) * z ^ 2 +
      (-controlBeta lam d c - controlAlpha lam d c * (lam + c.1)) * z +
      controlAlpha lam d c * u + controlH lam d 0 0 c := by
  unfold controlH controlAlpha controlBeta quadratic
  ring

theorem controlH_origin (lam : ℝ) (d : LowRankData) (c : Control) :
    controlH lam d 0 0 c = controlBeta lam d c * lam +
      controlAlpha lam d c * (lam * c.1 + c.1 ^ 2 / 2 + d.S) := by
  unfold controlH controlAlpha controlBeta quadratic
  ring

theorem Admissible.control_basic_bounded {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) :
    EssentiallyBounded (fun c : Control => primitive lam d c.1) controlMeasure ∧
    EssentiallyBounded (fun c : Control => quadratic lam (1 - c.1) - d.S) controlMeasure ∧
    EssentiallyBounded (fun c : Control => d.phi c.2.1) controlMeasure ∧
    EssentiallyBounded (fun c : Control => d.phi c.2.2) controlMeasure ∧
    EssentiallyBounded (fun c : Control => c.1) controlMeasure := by
  have hmem : ∀ᵐ c ∂controlMeasure, c ∈ controlDomain :=
    ae_restrict_mem controlDomain_measurable
  refine ⟨⟨2, ?_⟩, ⟨159 / 1000, ?_⟩, ⟨278 / 1000, ?_⟩,
    ⟨278 / 1000, ?_⟩, ⟨1, ?_⟩⟩
  · filter_upwards [hmem] with c hc
    rw [abs_of_nonneg (show 0 ≤ primitive lam d c.1 by
      linarith [h.control_R_lower hc.1])]
    exact h.control_R_upper hc.1
  · filter_upwards [hmem] with c hc
    rw [abs_of_nonneg (h.control_P_bounds hc.1).1]
    exact (h.control_P_bounds hc.1).2
  · filter_upwards [h.control_phi_bounds] with c hc
    simpa only [abs_of_nonneg hc.1.1] using hc.1.2
  · filter_upwards [h.control_phi_bounds] with c hc
    simpa only [abs_of_nonneg hc.2.1] using hc.2.2
  · filter_upwards [hmem] with c hc
    have hp := hc.1
    norm_num [pLo, pHi] at hp
    exact abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩

theorem Admissible.controlBeta_bounded {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) : EssentiallyBounded (controlBeta lam d) controlMeasure := by
  obtain ⟨hR, hP, hfx, hfy, _⟩ := h.control_basic_bounded
  have hnum := (hR.mul hfx).add (hP.mul hfy)
  apply hnum.div_of_abs_lower ((3 : ℝ) / 100) (by norm_num)
  have hmem : ∀ᵐ c ∂controlMeasure, c ∈ controlDomain :=
    ae_restrict_mem controlDomain_measurable
  filter_upwards [hmem] with c hc
  exact (h.determinant_positive hc).le.trans (le_abs_self _)

theorem Admissible.controlH_origin_bounded {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) :
    EssentiallyBounded (controlH lam d 0 0) controlMeasure := by
  have hA : EssentiallyBounded (controlAlpha lam d) controlMeasure :=
    ⟨19 / 2, h.controlAlpha_bound⟩
  have hp := h.control_basic_bounded.2.2.2.2
  have hpoly := ((EssentiallyBounded.const lam).mul hp).add
    ((hp.mul hp).mul (EssentiallyBounded.const (1 / 2)))
  have hb := (h.controlBeta_bounded.mul (EssentiallyBounded.const lam)).add
    (hA.mul (hpoly.add (EssentiallyBounded.const d.S)))
  convert hb using 1
  funext c
  rw [controlH_origin]
  ring

theorem Admissible.controlH_bounded {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (z u : ℝ) :
    EssentiallyBounded (controlH lam d z u) controlMeasure := by
  have hA : EssentiallyBounded (controlAlpha lam d) controlMeasure :=
    ⟨19 / 2, h.controlAlpha_bound⟩
  have hp := h.control_basic_bounded.2.2.2.2
  have hlin := h.controlBeta_bounded.neg.sub
    (hA.mul ((EssentiallyBounded.const lam).add hp))
  have hb := ((((hA.mul (EssentiallyBounded.const (1 / 2))).mul
    (EssentiallyBounded.const (z ^ 2))).add (hlin.mul (EssentiallyBounded.const z))).add
    (hA.mul (EssentiallyBounded.const u))).add h.controlH_origin_bounded
  convert hb using 1
  funext c
  rw [controlH_quadratic]
  ring

/-- Global state Lipschitz continuity of the actual essential-infimum ODE. -/
theorem Admissible.vectorField_lipschitz {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (z : ℝ) :
    LipschitzWith (19 / 2 : ℝ≥0) (vectorField lam d z) := by
  have he := lipschitz_affine_essInf (controlAlpha lam d) (controlH lam d z 0)
    (19 / 2) (by simpa using h.controlAlpha_bound) (h.controlH_bounded z 0)
  have he' : LipschitzWith (19 / 2 : ℝ≥0)
      (fun u => essInf (controlH lam d z u) controlMeasure) := by
    have hid : (fun u => essInf (controlH lam d z u) controlMeasure) =
        (fun u => essInf (fun c => controlAlpha lam d c * u + controlH lam d z 0 c)
          controlMeasure) := by
      funext u
      congr 1
      funext c
      exact controlH_affine lam d z u c
    rw [hid]
    exact he
  have hc : LipschitzWith (19 / 2 : ℝ≥0) (fun _ : ℝ => lam - z) :=
    (LipschitzWith.const (lam - z)).weaken (by positivity)
  change LipschitzWith (19 / 2 : ℝ≥0)
    (fun u => min (lam - z) (essInf (controlH lam d z u) controlMeasure))
  simpa only [max_self] using hc.min he' 

/-- The time dependence is continuous even while low-rank controls are only
measurable. This follows from uniformly bounded polynomial coefficients. -/
theorem Admissible.vectorField_continuous_time {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (u : ℝ) : Continuous (fun z => vectorField lam d z u) := by
  have hA : EssentiallyBounded (controlAlpha lam d) controlMeasure :=
    ⟨19 / 2, h.controlAlpha_bound⟩
  have hp := h.control_basic_bounded.2.2.2.2
  have hlin := h.controlBeta_bounded.neg.sub
    (hA.mul ((EssentiallyBounded.const lam).add hp))
  have he := continuous_affine2_essInf
    (fun c => controlAlpha lam d c / 2)
    (fun c => -controlBeta lam d c - controlAlpha lam d c * (lam + c.1))
    (fun c => controlAlpha lam d c * u + controlH lam d 0 0 c)
    (by simpa only [div_eq_mul_inv, one_div, one_mul] using
      hA.mul (EssentiallyBounded.const (1 / 2))) hlin
    ((hA.mul (EssentiallyBounded.const u)).add h.controlH_origin_bounded)
  have hf : Continuous (fun z : ℝ => (z ^ 2, z)) := by fun_prop
  have he' : Continuous (fun z => essInf (controlH lam d z u) controlMeasure) := by
    convert he.comp hf using 1
    funext z
    congr 1
    funext c
    rw [controlH_quadratic]
    ring
  exact (continuous_const.sub continuous_id).min he'

end OptimalG.Variational
