import OptimalG.VariationalWeakStar

/-! A solution of a time-continuous field with a uniform state Lipschitz
constant is Lipschitz, hence absolutely continuous, on every closed interval. -/
namespace OptimalG.Variational
open Set MeasureTheory
open scoped NNReal

theorem continuous_ode_solution_lipschitz {a b : ℝ} {F : ℝ → ℝ → ℝ} {Y : ℝ → ℝ}
    {K : ℝ≥0} (hF : ∀ z,LipschitzWith K (F z))
    (htime : ContinuousOn (fun z => F z 0) (Icc a b))
    (hY : ∀ z ∈ Icc a b,HasDerivWithinAt Y (F z (Y z)) (Icc a b) z) :
    ∃ M : ℝ≥0,LipschitzOnWith M Y (Icc a b) := by
  have hYc : ContinuousOn Y (Icc a b) := fun z hz => (hY z hz).continuousWithinAt
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hYc
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn htime
  let M : ℝ≥0 := ⟨K*max B 0+max C 0,by positivity⟩
  refine ⟨M,(convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hY ?_⟩
  intro z hz
  have hdist := (hF z).dist_le_mul (Y z) 0
  rw [dist_eq_norm,dist_zero_right] at hdist
  have htri := norm_add_le (F z (Y z)-F z 0) (F z 0)
  rw [sub_add_cancel] at htri
  have hyb : ‖Y z‖ ≤ max B 0 := (hB z hz).trans (le_max_left _ _)
  have hcb : ‖F z 0‖ ≤ max C 0 := (hC z hz).trans (le_max_left _ _)
  have hmult := mul_le_mul_of_nonneg_left hyb K.coe_nonneg
  change ‖F z (Y z)‖ ≤ (K : ℝ)*max B 0+max C 0
  exact htri.trans (add_le_add (hdist.trans hmult) hcb)

theorem continuous_ode_solution_absolutelyContinuous {a b : ℝ} {F : ℝ → ℝ → ℝ} {Y : ℝ → ℝ}
    {K : ℝ≥0} (hab : a ≤ b) (hF : ∀ z,LipschitzWith K (F z))
    (htime : ContinuousOn (fun z => F z 0) (Icc a b))
    (hY : ∀ z ∈ Icc a b,HasDerivWithinAt Y (F z (Y z)) (Icc a b) z) :
    AbsolutelyContinuousOnInterval Y a b := by
  obtain ⟨M,hM⟩ := continuous_ode_solution_lipschitz hF htime hY
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le hab] using hM

end OptimalG.Variational
