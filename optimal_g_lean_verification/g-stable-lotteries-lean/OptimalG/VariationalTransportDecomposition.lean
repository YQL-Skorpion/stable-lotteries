import OptimalG.VariationalTransportCauchy
import OptimalG.VariationalMatchingMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! Actual Lebesgue decomposition of the matched-rank derivative measure.
The singular term is a measure, not a silently discarded exceptional set. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter

variable {X : Type*} [MeasurableSpace X]

 theorem transport_measure_decomposition (Gamma mu : Measure X) [SigmaFinite Gamma] [SigmaFinite mu]
    {s : Set X} (hfinite : Gamma s ≠ ⊤) :
    (∫ r in s, (Gamma.rnDeriv mu r).toReal ∂mu)+(Gamma.singularPart mu).real s = Gamma.real s := by
  rw [Measure.setIntegral_toReal_rnDeriv_eq_withDensity]
  have h1 : (mu.withDensity (Gamma.rnDeriv mu)) s ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (Gamma.withDensity_rnDeriv_le mu s)
  have h2 : (Gamma.singularPart mu) s ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (Gamma.singularPart_le mu s)
  rw [measureReal_def,measureReal_def,measureReal_def,← ENNReal.toReal_add h1 h2,
    ← Measure.add_apply,Measure.rnDeriv_add_singularPart]

/-- Weighted decomposition, needed for the first-order rank term after Fubini. -/
theorem integral_transport_measure_decomposition (Gamma mu : Measure X)
    [SigmaFinite Gamma] [SigmaFinite mu] {f : X → ℝ} (hf : Integrable f Gamma) :
    (∫ r, f r ∂Gamma) = (∫ r, (Gamma.rnDeriv mu r).toReal*f r ∂mu)+
      (∫ r, f r ∂Gamma.singularPart mu) := by
  have hAC := hf.mono_measure (Gamma.withDensity_rnDeriv_le mu)
  have hsing := hf.mono_measure (Gamma.singularPart_le mu)
  calc
    (∫ r, f r ∂Gamma) = ∫ r, f r ∂(mu.withDensity (Gamma.rnDeriv mu)+Gamma.singularPart mu) := by
      rw [Measure.rnDeriv_add_singularPart]
    _ = (∫ r, f r ∂mu.withDensity (Gamma.rnDeriv mu))+(∫ r, f r ∂Gamma.singularPart mu) :=
      integral_add_measure hAC hsing
    _ = _ := by
      rw [integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv _ _) (Measure.rnDeriv_lt_top _ _)]
      rfl

 theorem setIntegral_transport_measure_decomposition (Gamma mu : Measure X)
    [SigmaFinite Gamma] [SigmaFinite mu] {s : Set X} (hs : MeasurableSet s)
    {f : X → ℝ} (hf : IntegrableOn f s Gamma) :
    (∫ r in s, f r ∂Gamma) = (∫ r in s, (Gamma.rnDeriv mu r).toReal*f r ∂mu)+
      (∫ r in s, f r ∂Gamma.singularPart mu) := by
  have h := integral_transport_measure_decomposition Gamma mu ((integrable_indicator_iff hs).2 hf)
  have he : (fun r => (Gamma.rnDeriv mu r).toReal*s.indicator f r) =
      s.indicator (fun r => (Gamma.rnDeriv mu r).toReal*f r) := by
    funext r
    by_cases hr : r ∈ s <;> simp [hr]
  rw [he,integral_indicator hs,integral_indicator hs,integral_indicator hs] at h
  exact h

 theorem integrableOn_transport_rn_mul (Gamma mu : Measure X)
    [SigmaFinite Gamma] [SigmaFinite mu] {s : Set X} (hs : MeasurableSet s)
    {f : X → ℝ} (hf : IntegrableOn f s Gamma) :
    IntegrableOn (fun r => (Gamma.rnDeriv mu r).toReal*f r) s mu := by
  have hi : Integrable (s.indicator f) Gamma := (integrable_indicator_iff hs).2 hf
  have hw : Integrable (fun r => (Gamma.rnDeriv mu r).toReal*s.indicator f r) mu :=
    (integrable_withDensity_iff_integrable_smul' (Measure.measurable_rnDeriv _ _)
      (Measure.rnDeriv_lt_top _ _)).mp (hi.mono_measure (Gamma.withDensity_rnDeriv_le mu))
  have he : (fun r => (Gamma.rnDeriv mu r).toReal*s.indicator f r) =
      s.indicator (fun r => (Gamma.rnDeriv mu r).toReal*f r) := by
    funext r
    by_cases hr : r ∈ s <;> simp [hr]
  rw [he] at hw
  exact (integrable_indicator_iff hs).1 hw

 theorem transportVariationDensity_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ transportVariationDensity x ∧ transportVariationDensity x ≤ x+1 := by
  have hden : 0 < x+1 := by linarith
  constructor
  · exact div_nonneg (sq_nonneg _) hden.le
  · change (x-1)^2/(x+1) ≤ x+1
    apply (div_le_iff₀ hden).2
    nlinarith

 theorem transport_rn_variation_integrable (Gamma mu : Measure X) [SigmaFinite Gamma] [SigmaFinite mu]
    {s : Set X} (hfinite : Gamma s ≠ ⊤) [IsFiniteMeasure (mu.restrict s)] :
    IntegrableOn (fun r => transportVariationDensity (Gamma.rnDeriv mu r).toReal) s mu := by
  have hxi : IntegrableOn (fun r => (Gamma.rnDeriv mu r).toReal) s mu :=
    Measure.integrableOn_toReal_rnDeriv hfinite
  have hm := (Measure.measurable_rnDeriv Gamma mu).ennreal_toReal
  have hvar : Measurable (fun r => transportVariationDensity (Gamma.rnDeriv mu r).toReal) :=
    ((hm.sub_const 1).pow_const 2).div (hm.add_const 1)
  apply (hxi.add (integrable_const 1)).mono' hvar.aestronglyMeasurable
  filter_upwards [] with r
  have h := transportVariationDensity_bounds (ENNReal.toReal_nonneg : 0 ≤ (Gamma.rnDeriv mu r).toReal)
  rw [Real.norm_eq_abs,abs_of_nonneg h.1]
  exact h.2

 theorem stieltjes_deriv_rn_ae (G : StieltjesFunction ℝ) :
    deriv G =ᵐ[volume] fun r => (G.measure.rnDeriv volume r).toReal := by
  filter_upwards [G.ae_hasDerivAt] with r hr
  exact hr.deriv

/-- The cumulative displacement is the integral of gamma'-1 plus the
singular derivative mass, including the left endpoint atom. -/
theorem stieltjes_displacement_decomposition (G : StieltjesFunction ℝ)
    {a r : ℝ} (har : a ≤ r) (hleft : Function.leftLim G a = a) :
    G r-r = (∫ t in Icc a r, deriv G t-1)+(G.measure.singularPart volume).real (Icc a r) := by
  have hfinite : G.measure (Icc a r) ≠ ⊤ := (isCompact_Icc.measure_lt_top).ne
  have hdecomp := transport_measure_decomposition G.measure volume hfinite
  have hderEq : (∫ t in Icc a r, deriv G t) = ∫ t in Icc a r, (G.measure.rnDeriv volume t).toReal :=
    integral_congr_ae (ae_restrict_of_ae (stieltjes_deriv_rn_ae G))
  have hderInt : IntegrableOn (deriv G) (Icc a r) :=
    (Measure.integrableOn_toReal_rnDeriv hfinite).congr (ae_restrict_of_ae (stieltjes_deriv_rn_ae G).symm)
  have hlow : a ≤ G r := by
    rw [← hleft]
    exact G.mono.leftLim_le har
  have hmass : G.measure.real (Icc a r) = G r-a := by
    rw [measureReal_def,G.measure_Icc,hleft,ENNReal.toReal_ofReal (sub_nonneg.mpr hlow)]
  rw [hmass,← hderEq] at hdecomp
  rw [integral_sub hderInt (integrable_const 1),integral_const]
  simp only [smul_eq_mul,mul_one,measureReal_restrict_apply_univ,Real.volume_real_Icc,max_eq_left (sub_nonneg.mpr har)] at *
  linarith

end OptimalG.Variational
