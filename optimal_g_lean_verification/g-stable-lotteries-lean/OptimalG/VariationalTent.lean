import OptimalG.VariationalAverages

/-!
# Continuous near-minimizing averages

The tent weight `max(0,m+eps-v)` vanishes above the epsilon sublevel. Its
normalization gives an explicit averaged control between the envelope and the
envelope plus epsilon. Including the line branch as a separate atom avoids
any measurable-selection hypothesis.
-/

namespace OptimalG.Variational

open Set MeasureTheory Filter
open scoped NNReal Topology

noncomputable def tentWeight (m eps v : ℝ) : ℝ := max 0 (m + eps - v)

theorem tentWeight_nonneg (m eps v : ℝ) : 0 ≤ tentWeight m eps v := le_max_left _ _

theorem tentWeight_mul_le (m eps v : ℝ) :
    tentWeight m eps v * v ≤ tentWeight m eps v * (m + eps) := by
  by_cases hv : v ≤ m + eps
  · exact mul_le_mul_of_nonneg_left hv (tentWeight_nonneg _ _ _)
  · have hw : tentWeight m eps v = 0 := max_eq_left (by linarith)
    rw [hw]
    simp

theorem tentWeight_le_eps (m eps v : ℝ) (heps : 0 ≤ eps) (hv : m ≤ v) :
    tentWeight m eps v ≤ eps := max_le heps (by linarith)

variable {I : Type*} [MeasurableSpace I] {mu : Measure I}

theorem EssentiallyBounded.tentWeight {f : I → ℝ} (hf : EssentiallyBounded f mu)
    (m eps : ℝ) : EssentiallyBounded (fun i => tentWeight m eps (f i)) mu := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨|m + eps| + |B|, ?_⟩
  filter_upwards [hB] with i hi
  rw [abs_of_nonneg (tentWeight_nonneg _ _ _)]
  unfold OptimalG.Variational.tentWeight
  apply max_le (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hf := (abs_le.mp hi).1
  linarith [le_abs_self (m + eps), le_abs_self B]

theorem aestronglyMeasurable_tentWeight {f : I → ℝ}
    (hf : AEStronglyMeasurable f mu) (m eps : ℝ) :
    AEStronglyMeasurable (fun i => tentWeight m eps (f i)) mu :=
  aestronglyMeasurable_const.sup (aestronglyMeasurable_const.sub hf)

/-- The denominator of the tent average is strictly positive. -/
theorem tent_denominator_pos [NeZero mu] [IsFiniteMeasure mu]
    (f : I → ℝ) (l eps : ℝ) (heps : 0 < eps)
    (hf : EssentiallyBounded f mu) (hmeas : AEStronglyMeasurable f mu) :
    0 < tentWeight (min l (essInf f mu)) eps l +
      ∫ i, tentWeight (min l (essInf f mu)) eps (f i) ∂mu := by
  by_cases hl : l ≤ essInf f mu
  · rw [min_eq_left hl]
    have hw : tentWeight l eps l = eps := by unfold tentWeight; rw [add_sub_cancel_left, max_eq_right heps.le]
    rw [hw]
    exact add_pos_of_pos_of_nonneg heps (integral_nonneg (fun _ => tentWeight_nonneg _ _ _))
  · rw [min_eq_right (le_of_not_ge hl)]
    have hwi := (hf.tentWeight (essInf f mu) eps).integrable (aestronglyMeasurable_tentWeight hmeas _ _)
    have hsupport : 0 < mu (Function.support (fun i => tentWeight (essInf f mu) eps (f i))) := by
      apply (essInf_sublevel_positive f hf heps).trans_le
      apply measure_mono
      intro i hi
      change f i < essInf f mu + eps at hi
      change tentWeight (essInf f mu) eps (f i) ≠ 0
      have hp : 0 < tentWeight (essInf f mu) eps (f i) :=
        lt_max_of_lt_right (by linarith [hi])
      exact hp.ne'
    have hwpos := (integral_pos_iff_support_of_nonneg
      (fun _ => tentWeight_nonneg (essInf f mu) eps _) hwi).mpr hsupport
    exact add_pos_of_nonneg_of_pos (tentWeight_nonneg _ _ _) hwpos

noncomputable def tentAverage {I : Type*} [MeasurableSpace I] (mu : Measure I)
    (f : I → ℝ) (l eps : ℝ) : ℝ :=
  let m := min l (essInf f mu)
  (tentWeight m eps l * l + ∫ i, tentWeight m eps (f i) * f i ∂mu) /
    (tentWeight m eps l + ∫ i, tentWeight m eps (f i) ∂mu)

/-- The explicit probability average of the line branch and the rational
controls is within epsilon of their essential-infimum envelope. -/
theorem tentAverage_bounds [NeZero mu] [IsFiniteMeasure mu]
    (f : I → ℝ) (l eps : ℝ) (heps : 0 < eps)
    (hf : EssentiallyBounded f mu) (hmeas : AEStronglyMeasurable f mu) :
    min l (essInf f mu) ≤ tentAverage mu f l eps ∧
      tentAverage mu f l eps ≤ min l (essInf f mu) + eps := by
  let m := min l (essInf f mu)
  let w : I → ℝ := fun i => tentWeight m eps (f i)
  have hw : EssentiallyBounded w mu := hf.tentWeight m eps
  have hwm : AEStronglyMeasurable w mu := aestronglyMeasurable_tentWeight hmeas m eps
  have hwi := hw.integrable hwm
  have hwfi := (hw.mul hf).integrable (hwm.mul hmeas)
  have hlo : ∀ᵐ i ∂mu, w i * m ≤ w i * f i := by
    filter_upwards [ae_essInf_le hf.boundedBelow] with i hi
    exact mul_le_mul_of_nonneg_left ((min_le_right l _).trans hi) (tentWeight_nonneg _ _ _)
  have hhi : ∀ᵐ i ∂mu, w i * f i ≤ w i * (m + eps) :=
    Eventually.of_forall (fun i => tentWeight_mul_le m eps (f i))
  have hloint := integral_mono_ae (hwi.mul_const m) hwfi hlo
  have hhiint := integral_mono_ae hwfi (hwi.mul_const (m + eps)) hhi
  rw [integral_mul_const] at hloint hhiint
  have hlineLo : tentWeight m eps l * m ≤ tentWeight m eps l * l :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) (tentWeight_nonneg _ _ _)
  have hlineHi := tentWeight_mul_le m eps l
  have hden := tent_denominator_pos f l eps heps hf hmeas
  change 0 < tentWeight m eps l + ∫ i, w i ∂mu at hden
  change m ≤ (tentWeight m eps l * l + ∫ i, w i * f i ∂mu) /
      (tentWeight m eps l + ∫ i, w i ∂mu) ∧
    (tentWeight m eps l * l + ∫ i, w i * f i ∂mu) /
      (tentWeight m eps l + ∫ i, w i ∂mu) ≤ m + eps
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith
  · apply (div_le_iff₀ hden).mpr
    nlinarith

/-- Continuity of a tent-weighted moment. The minorant condition bounds every
weight by epsilon, so no uniform modulus in the control variable is needed. -/
theorem continuousOn_tent_moment
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [IsFiniteMeasure mu] (s : Set X) (F G : X → I → ℝ) (m : X → ℝ)
    (eps C : ℝ) (heps : 0 ≤ eps)
    (hm : ContinuousOn m s)
    (hFm : ∀ x ∈ s, AEStronglyMeasurable (F x) mu)
    (hGm : ∀ x ∈ s, AEStronglyMeasurable (G x) mu)
    (hFc : ∀ᵐ i ∂mu, ContinuousOn (fun x => F x i) s)
    (hGc : ∀ᵐ i ∂mu, ContinuousOn (fun x => G x i) s)
    (hminor : ∀ x ∈ s, ∀ᵐ i ∂mu, m x ≤ F x i)
    (hGbound : ∀ x ∈ s, ∀ᵐ i ∂mu, |G x i| ≤ C) :
    ContinuousOn (fun x => ∫ i, tentWeight (m x) eps (F x i) * G x i ∂mu) s := by
  apply continuousOn_of_dominated (bound := fun _ => eps * |C|)
  · intro x hx
    exact (aestronglyMeasurable_tentWeight (hFm x hx) (m x) eps).mul (hGm x hx)
  · intro x hx
    filter_upwards [hminor x hx, hGbound x hx] with i hmi hgi
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tentWeight_nonneg _ _ _)]
    exact mul_le_mul (tentWeight_le_eps _ _ _ heps hmi)
      (hgi.trans (le_abs_self C)) (abs_nonneg _) heps
  · exact integrable_const _
  · filter_upwards [hFc, hGc] with i hfi hgi
    have hw : ContinuousOn (fun x => max 0 (m x + eps - F x i)) s := by
      fun_prop
    exact hw.mul hgi

end OptimalG.Variational
