import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Normalizing a completed centered activation

The final normalization in Section 5.3 is verified here. The existence of the
completed curve is NOT assumed globally: each theorem explicitly takes the
necessary regularity, monotonicity, endpoint, or integral hypotheses. All
regularity hypotheses concern the actual interval `[0,1]`.
-/

namespace OptimalG

open Set MeasureTheory

/-- Normalization used in Section 5.3 of the manuscript. -/
noncomputable def normalizedActivation (phi : ℝ → ℝ) (r : ℝ) : ℝ :=
  (phi 0 - phi r) / (1 + phi 0)

theorem normalization_denominator_pos {phi : ℝ → ℝ}
    (hanti : StrictAntiOn phi (Icc 0 1)) (hend : phi 1 = -1) :
    0 < 1 + phi 0 := by
  have h := hanti (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show (0 : ℝ) < 1 by norm_num)
  rw [hend] at h
  linarith

theorem normalizedActivation_continuousOn {phi : ℝ → ℝ}
    (hcont : ContinuousOn phi (Icc 0 1)) :
    ContinuousOn (normalizedActivation phi) (Icc 0 1) := by
  exact (continuousOn_const.sub hcont).div_const (1 + phi 0)

theorem normalizedActivation_strictMonoOn {phi : ℝ → ℝ}
    (hanti : StrictAntiOn phi (Icc 0 1)) (hend : phi 1 = -1) :
    StrictMonoOn (normalizedActivation phi) (Icc 0 1) := by
  intro x hx y hy hxy
  have hden := normalization_denominator_pos hanti hend
  have h := hanti hx hy hxy
  dsimp [normalizedActivation]
  exact (div_lt_div_iff_of_pos_right hden).mpr (by linarith)

@[simp] theorem normalizedActivation_zero (phi : ℝ → ℝ) :
    normalizedActivation phi 0 = 0 := by
  simp [normalizedActivation]

theorem normalizedActivation_one {phi : ℝ → ℝ}
    (hanti : StrictAntiOn phi (Icc 0 1)) (hend : phi 1 = -1) :
    normalizedActivation phi 1 = 1 := by
  have hden := ne_of_gt (normalization_denominator_pos hanti hend)
  dsimp [normalizedActivation]
  rw [hend]
  convert div_self hden using 1
  ring

theorem normalizedActivation_mem_Icc {phi : ℝ → ℝ}
    (hanti : StrictAntiOn phi (Icc 0 1)) (hend : phi 1 = -1)
    {r : ℝ} (hr : r ∈ Icc 0 1) : normalizedActivation phi r ∈ Icc 0 1 := by
  have hmono := (normalizedActivation_strictMonoOn hanti hend).monotoneOn
  constructor
  · have h := hmono (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) hr hr.1
    simpa using h
  · have h := hmono hr (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) hr.2
    simpa [normalizedActivation_one hanti hend] using h

/-- Zero mean of the centered curve gives exactly the stated activation mean. -/
theorem normalizedActivation_integral {phi : ℝ → ℝ}
    (hcont : ContinuousOn phi (Icc 0 1))
    (hzero : (∫ r in (0 : ℝ)..1, phi r) = 0) :
    (∫ r in (0 : ℝ)..1, normalizedActivation phi r) = phi 0 / (1 + phi 0) := by
  have hint : IntervalIntegrable phi volume 0 1 :=
    hcont.intervalIntegrable_of_Icc (by norm_num)
  simp only [normalizedActivation, intervalIntegral.integral_div]
  rw [intervalIntegral.integral_sub intervalIntegrable_const hint]
  simp [hzero]

/-- The rescaling recovers the original centered curve pointwise. -/
theorem centered_normalizedActivation {phi : ℝ → ℝ}
    (hanti : StrictAntiOn phi (Icc 0 1)) (hend : phi 1 = -1) (r : ℝ) :
    (1 + phi 0) * (phi 0 / (1 + phi 0) - normalizedActivation phi r) = phi r := by
  have hden := ne_of_gt (normalization_denominator_pos hanti hend)
  dsimp [normalizedActivation]
  field_simp
  ring

/-- Complete verified normalization, conditional on a completed centered curve.
This packages no variational or numerical claims into its premises. -/
theorem completed_curve_yields_activation {phi : ℝ → ℝ}
    (hcont : ContinuousOn phi (Icc 0 1))
    (hanti : StrictAntiOn phi (Icc 0 1))
    (hend : phi 1 = -1)
    (hzero : (∫ r in (0 : ℝ)..1, phi r) = 0) :
    ContinuousOn (normalizedActivation phi) (Icc 0 1) ∧
    StrictMonoOn (normalizedActivation phi) (Icc 0 1) ∧
    normalizedActivation phi 0 = 0 ∧
    normalizedActivation phi 1 = 1 ∧
    (∀ r ∈ Icc (0 : ℝ) 1, normalizedActivation phi r ∈ Icc 0 1) ∧
    (∫ r in (0 : ℝ)..1, normalizedActivation phi r) = phi 0 / (1 + phi 0) := by
  exact ⟨normalizedActivation_continuousOn hcont,
    normalizedActivation_strictMonoOn hanti hend,
    normalizedActivation_zero phi,
    normalizedActivation_one hanti hend,
    fun _ hr => normalizedActivation_mem_Icc hanti hend hr,
    normalizedActivation_integral hcont hzero⟩

end OptimalG
