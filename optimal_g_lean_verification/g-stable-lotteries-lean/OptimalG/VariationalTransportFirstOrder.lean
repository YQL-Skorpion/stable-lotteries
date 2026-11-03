import OptimalG.VariationalTransportDecomposition
import OptimalG.VariationalTransportFubini

/-! The first-order term of (B.11), including the singular mass and the
boundary displacement, derived from Fubini and the actual Lebesgue decomposition. -/
namespace OptimalG.Variational
open Set MeasureTheory

noncomputable def transportPotential (mu : Measure ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ r in Ici t, f r ∂mu

 theorem transport_first_order_decomposition {mu Gamma : Measure ℝ}
    [IsFiniteMeasure mu] [IsFiniteMeasure Gamma] {f : ℝ → ℝ}
    (hf : Integrable f mu) :
    (∫ r, f r*(Gamma.real (Iic r)-mu.real (Iic r)) ∂mu) =
      (∫ r, transportPotential mu f r*((Gamma.rnDeriv mu r).toReal-1) ∂mu)+
      (∫ r, transportPotential mu f r ∂Gamma.singularPart mu) := by
  have hPmu : Integrable (transportPotential mu f) mu := cumulative_potential_integrable hf
  have hPG : Integrable (transportPotential mu f) Gamma := cumulative_potential_integrable hf
  have hweighted : Integrable (fun r => (Gamma.rnDeriv mu r).toReal*transportPotential mu f r) mu := by
    exact (integrable_withDensity_iff_integrable_smul' (Measure.measurable_rnDeriv _ _)
      (Measure.rnDeriv_lt_top _ _)).mp (hPG.mono_measure (Gamma.withDensity_rnDeriv_le mu))
  rw [cumulative_displacement_fubini hf]
  change (∫ r, transportPotential mu f r ∂Gamma)-(∫ r, transportPotential mu f r ∂mu) = _
  rw [integral_transport_measure_decomposition Gamma mu hPG]
  have hi : (∫ r, transportPotential mu f r*((Gamma.rnDeriv mu r).toReal-1) ∂mu) =
      (∫ r, (Gamma.rnDeriv mu r).toReal*transportPotential mu f r ∂mu)-
      (∫ r, transportPotential mu f r ∂mu) := by
    have he : (fun r => transportPotential mu f r*((Gamma.rnDeriv mu r).toReal-1)) =
        (fun r => (Gamma.rnDeriv mu r).toReal*transportPotential mu f r-transportPotential mu f r) := by
      funext r
      ring
    rw [he,integral_sub hweighted hPmu]
  rw [hi]
  ring

/-- The constant k produces the full boundary mass; no initial atom has
been removed from the singular measure. -/
theorem transport_first_order_centered {mu nu : Measure ℝ}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] {P W xi : ℝ → ℝ} {k eb : ℝ}
    (hxi : Integrable (fun r => xi r-1) mu)
    (hP : Integrable (fun r => P r*(xi r-1)) mu)
    (hW : Integrable (fun r => W r*(xi r-1)) mu)
    (hPnu : Integrable P nu)
    (hmass : (∫ r, xi r-1 ∂mu)+nu.real univ = eb) :
    (∫ r, P r*(xi r-1) ∂mu)+(∫ r, P r ∂nu)-(∫ r, W r*(xi r-1) ∂mu) =
      k*eb+(∫ r, (P r-W r-k)*(xi r-1) ∂mu)+(∫ r, P r-k ∂nu) := by
  have hac : (∫ r, (P r-W r-k)*(xi r-1) ∂mu) =
      (∫ r, P r*(xi r-1) ∂mu)-(∫ r, W r*(xi r-1) ∂mu)-k*(∫ r, xi r-1 ∂mu) := by
    have he : (fun r => (P r-W r-k)*(xi r-1)) =
        (fun r => P r*(xi r-1)-W r*(xi r-1)-k*(xi r-1)) := by funext r; ring
    have hPW : Integrable (fun r => P r*(xi r-1)-W r*(xi r-1)) mu := hP.sub hW
    rw [he,integral_sub hPW (hxi.const_mul k),integral_sub hP hW,integral_const_mul]
  have hsing : (∫ r, P r-k ∂nu) = (∫ r, P r ∂nu)-k*nu.real univ := by
    rw [integral_sub hPnu (integrable_const k),integral_const]
    simp only [smul_eq_mul,mul_comm]
  rw [hac,hsing,← hmass]
  ring

end OptimalG.Variational
