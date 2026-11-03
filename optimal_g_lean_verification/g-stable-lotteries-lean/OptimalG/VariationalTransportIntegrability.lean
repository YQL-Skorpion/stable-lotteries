import OptimalG.VariationalTransportIntegral

/-! Integrability of the actual entropy density; the lower bound on the
matched derivative comes from the bounded original score. -/
namespace OptimalG.Variational
open MeasureTheory Real

 theorem reciprocal_matched_derivative_le {score xi m m0 M : ℝ}
    (hxi : 0 < xi) (hm0 : 0 < m0) (hscore : score ≤ M)
    (hmatch : score*xi = m) (hm : m0 ≤ m) : 1/xi ≤ M/m0 := by
  apply (div_le_div_iff₀ hxi hm0).2
  have h := mul_le_mul_of_nonneg_right hscore hxi.le
  nlinarith only [h,hmatch,hm]

variable {X : Type*} [MeasurableSpace X]

theorem transportEntropy_integrable {mu : Measure X} [IsFiniteMeasure mu]
    {xi : X → ℝ} {delta : ℝ} (hxi : Integrable xi mu) (hdelta : 0 < delta)
    (hlower : ∀ᵐ r ∂mu, delta ≤ xi r) : Integrable (fun r => transportEntropy (xi r)) mu := by
  have hlog : AEMeasurable (fun r => log (xi r)) mu :=
    Real.measurable_log.comp_aemeasurable hxi.aemeasurable
  have hmeas : AEStronglyMeasurable (fun r => transportEntropy (xi r)) mu :=
    (hxi.aestronglyMeasurable.sub aestronglyMeasurable_const).sub hlog.aestronglyMeasurable
  apply (hxi.add (integrable_const (|log delta|+1))).mono' hmeas
  filter_upwards [hlower] with r hr
  have hpos : 0 < xi r := hdelta.trans_le hr
  rw [Real.norm_eq_abs,abs_of_nonneg (transportEntropy_nonneg hpos)]
  have hl := Real.log_le_log hdelta hr
  have ha := neg_abs_le (log delta)
  unfold transportEntropy
  change xi r-1-log (xi r) ≤ xi r+(|log delta|+1)
  linarith

end OptimalG.Variational
