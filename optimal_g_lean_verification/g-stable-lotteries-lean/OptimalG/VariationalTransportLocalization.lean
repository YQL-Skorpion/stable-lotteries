import OptimalG.VariationalTransportDecomposition

/-! Uniform displacement control for the actual Stieltjes matching,
including its initial atom and all singular derivative mass. -/
namespace OptimalG.Variational
open Set MeasureTheory

noncomputable def matchingVariation (G : StieltjesFunction ℝ) (a b : ℝ) : ℝ :=
  (∫ r in Icc a b, transportVariationDensity (deriv G r))+
    (G.measure.singularPart volume).real (Icc a b)

 theorem stieltjes_deriv_integrable (G : StieltjesFunction ℝ) (a b : ℝ) :
    IntegrableOn (deriv G) (Icc a b) := by
  have hfinite : G.measure (Icc a b) ≠ ⊤ := (isCompact_Icc.measure_lt_top).ne
  exact (Measure.integrableOn_toReal_rnDeriv hfinite).congr
    (ae_restrict_of_ae (stieltjes_deriv_rn_ae G).symm)

 theorem stieltjes_variation_integrable (G : StieltjesFunction ℝ) (a b : ℝ) :
    IntegrableOn (fun r => transportVariationDensity (deriv G r)) (Icc a b) := by
  have hfinite : G.measure (Icc a b) ≠ ⊤ := (isCompact_Icc.measure_lt_top).ne
  apply (transport_rn_variation_integrable G.measure volume hfinite).congr
  filter_upwards [ae_restrict_of_ae (stieltjes_deriv_rn_ae G)] with r hr
  rw [hr]

 theorem matchingVariation_nonneg (G : StieltjesFunction ℝ) (a b : ℝ) :
    0 ≤ matchingVariation G a b := by
  apply add_nonneg _ measureReal_nonneg
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_of_ae (stieltjes_deriv_rn_ae G)] with r hr
  rw [hr]
  exact (transportVariationDensity_bounds ENNReal.toReal_nonneg).1

 theorem stieltjes_displacement_sq_bound (G : StieltjesFunction ℝ) {a b r : ℝ}
    (hab : a ≤ b) (hleft : Function.leftLim G a = a) (hend : G b ≤ b)
    (hpos : ∀ᵐ s ∂volume.restrict (Icc a b), 0 < deriv G s) (hr : r ∈ Icc a b) :
    (G r-r)^2 ≤ 2*(b-a)*matchingVariation G a b := by
  have hsub : Icc a r ⊆ Icc a b := Icc_subset_Icc_right hr.2
  have hfinite : G.measure (Icc a b) ≠ ⊤ := (isCompact_Icc.measure_lt_top).ne
  have hsingfinite : (G.measure.singularPart volume) (Icc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (G.measure.singularPart_le volume _)
  have hder := stieltjes_deriv_integrable G a r
  have hvar := stieltjes_variation_integrable G a r
  have hposr := ae_restrict_of_ae_restrict_of_subset hsub hpos
  have hsigma : 0 ≤ (G.measure.singularPart volume).real (Icc a r) := measureReal_nonneg
  have hdisp := stieltjes_displacement_decomposition G hr.1 hleft
  have hcauchy := transport_displacement_sq_le_all hder hposr hvar hsigma
  rw [← hdisp] at hcauchy
  have hconst : (∫ s in Icc a r, (1:ℝ)) = r-a := by
    rw [integral_const]
    simp only [smul_eq_mul,mul_one,measureReal_restrict_apply_univ,Real.volume_real_Icc,max_eq_left (sub_nonneg.mpr hr.1)]
  have hmass : (∫ s in Icc a r, deriv G s+1)+(G.measure.singularPart volume).real (Icc a r) =
      G r+r-2*a := by
    rw [integral_add hder (integrable_const 1),hconst]
    rw [integral_sub hder (integrable_const 1),hconst] at hdisp
    linarith
  have hupper : G r+r-2*a ≤ 2*(b-a) := by
    have hh := (G.mono hr.2).trans hend
    linarith [hr.2]
  have hvarnonneg : ∀ᵐ s ∂volume.restrict (Icc a b), 0 ≤ transportVariationDensity (deriv G s) := by
    filter_upwards [hpos] with s hs
    exact (transportVariationDensity_bounds hs.le).1
  have hvarmono : matchingVariation G a r ≤ matchingVariation G a b := by
    apply add_le_add
    · exact setIntegral_mono_set (stieltjes_variation_integrable G a b) hvarnonneg
        (Filter.Eventually.of_forall hsub)
    · exact measureReal_mono hsub hsingfinite
  rw [hmass] at hcauchy
  calc
    (G r-r)^2 ≤ (G r+r-2*a)*matchingVariation G a r := hcauchy
    _ ≤ (2*(b-a))*matchingVariation G a r :=
      mul_le_mul_of_nonneg_right hupper (matchingVariation_nonneg G a r)
    _ ≤ (2*(b-a))*matchingVariation G a b :=
      mul_le_mul_of_nonneg_left hvarmono (by linarith)

end OptimalG.Variational
