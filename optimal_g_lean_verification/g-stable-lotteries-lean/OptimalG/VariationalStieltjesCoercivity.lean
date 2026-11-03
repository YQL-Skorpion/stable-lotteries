import OptimalG.VariationalStieltjesFirstOrder
import OptimalG.VariationalTransportLocalization
import OptimalG.VariationalTransportConsequences

/-! The actual Stieltjes first variation feeds the reference coercivity
bound. No singular part or initial endpoint atom is dropped. -/
namespace OptimalG.Variational
open Set MeasureTheory Function

 theorem tail_potential_integrable {a b : ℝ} {nu : Measure ℝ}
    [IsFiniteMeasure (nu.restrict (Icc a b))] {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc a b)) :
    IntegrableOn (fun r => ∫ t in r..b, f t) (Icc a b) nu := by
  have h := cumulative_potential_integrable (nu:=nu.restrict (Icc a b)) hf
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  exact transportPotential_interval_eq hr f

 theorem stieltjes_potential_derivative_integrable (G : StieltjesFunction ℝ) {a b : ℝ}
    {f : ℝ → ℝ} (hf : IntegrableOn f (Icc a b)) :
    IntegrableOn (fun r => (∫ t in r..b, f t)*(deriv G r-1)) (Icc a b) := by
  letI : IsFiniteMeasure (G.measure.restrict (Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
  have hPG : IntegrableOn (fun r => ∫ t in r..b, f t) (Icc a b) G.measure := tail_potential_integrable hf
  have hPmu : IntegrableOn (fun r => ∫ t in r..b, f t) (Icc a b) := tail_potential_integrable hf
  have hRN := integrableOn_transport_rn_mul G.measure volume measurableSet_Icc hPG
  have hder : IntegrableOn (fun r => deriv G r*(∫ t in r..b, f t)) (Icc a b) := by
    apply hRN.congr
    filter_upwards [ae_restrict_of_ae (stieltjes_deriv_rn_ae G)] with r hr
    rw [hr]
  have hi := hder.sub hPmu
  apply hi.congr
  filter_upwards [] with r
  simp only [Pi.sub_apply]
  ring

 theorem stieltjes_first_order_centered (G : StieltjesFunction ℝ) {a b k : ℝ}
    (hab : a ≤ b) (hleft : leftLim G a = a) {f W : ℝ → ℝ}
    (hf : IntegrableOn f (Icc a b))
    (hW : IntegrableOn (fun r => W r*(deriv G r-1)) (Icc a b)) :
    (∫ r in Icc a b, f r*(G r-r))-(∫ r in Icc a b, W r*(deriv G r-1)) =
      k*(G b-b)+
      (∫ r in Icc a b, ((∫ t in r..b, f t)-W r-k)*(deriv G r-1))+
      (∫ r in Icc a b, (∫ t in r..b, f t)-k ∂G.measure.singularPart volume) := by
  have hfinite : (G.measure.singularPart volume) (Icc a b) < ⊤ :=
    lt_of_le_of_lt (G.measure.singularPart_le volume _) isCompact_Icc.measure_lt_top
  letI : IsFiniteMeasure ((G.measure.singularPart volume).restrict (Icc a b)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite⟩
  have hmass := stieltjes_displacement_decomposition G hab hleft
  have hxi : IntegrableOn (fun r => deriv G r-1) (Icc a b) :=
    (stieltjes_deriv_integrable G a b).sub (integrable_const 1)
  have h := transport_first_order_centered (k:=k) hxi
    (stieltjes_potential_derivative_integrable G hf) hW (tail_potential_integrable hf)
    (by simpa only [measureReal_restrict_apply_univ] using hmass.symm)
  rw [stieltjes_first_order_transport G hleft hf]
  exact h

/-- The comparison supplied by the logarithmic ODE, coefficient Taylor
bounds, and exact pushforwards yields the numerical coercivity statement. -/
theorem stieltjes_reference_coercivity (G : StieltjesFunction ℝ) {a b : ℝ}
    (hab : a ≤ b) (hleft : leftLim G a = a) (hend : G b ≤ b)
    {f W : ℝ → ℝ} {W0 k A A0 kappa ds Krank eps Lref initial Lambda : ℝ}
    (hf : IntegrableOn f (Icc a b))
    (hWlin : IntegrableOn (fun r => W r*(deriv G r-1)) (Icc a b))
    (hW0 : 0 ≤ W0) (hk : k ≤ 0)
    (hW : ∀ᵐ r ∂volume.restrict (Icc a b), W0 ≤ W r)
    (ha : ∀ r ∈ Icc a b, 0 < (∫ t in r..b, f t)-k-W0)
    (hxi : ∀ᵐ r ∂volume.restrict (Icc a b), 0 < deriv G r)
    (herr : IntegrableOn (fun r => ((∫ t in r..b, f t)-W r-k)^2/
      ((∫ t in r..b, f t)-k-W0)) (Icc a b))
    (hent : IntegrableOn (fun r => W r*transportEntropy (deriv G r)) (Icc a b))
    (heps : (∫ r in Icc a b, ((∫ t in r..b, f t)-W r-k)^2/
      ((∫ t in r..b, f t)-k-W0)) ≤ eps)
    (hkappa : 0 < kappa) (hA : |A| ≤ A0)
    (hflowTaylor : Lref+initial+A*ds+(∫ r in Icc a b, f r*(G r-r))-
      (∫ r in Icc a b, W r*(deriv G r-1))+
      (∫ r in Icc a b, W r*transportEntropy (deriv G r))+kappa*ds^2-
      Krank*matchingVariation G a b ≤ Lambda) :
    Lref+initial-eps-A0^2/(4*kappa)+((8:ℝ)/9*W0-Krank)*matchingVariation G a b ≤ Lambda := by
  have hfinite : (G.measure.singularPart volume) (Icc a b) < ⊤ :=
    lt_of_le_of_lt (G.measure.singularPart_le volume _) isCompact_Icc.measure_lt_top
  letI : IsFiniteMeasure ((G.measure.singularPart volume).restrict (Icc a b)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite⟩
  have hPnu : IntegrableOn (fun r => (∫ t in r..b, f t)-k) (Icc a b)
      (G.measure.singularPart volume) := (tail_potential_integrable hf).sub (integrable_const k)
  have hlin : IntegrableOn (fun r => ((∫ t in r..b, f t)-W r-k)*(deriv G r-1)) (Icc a b) := by
    have hi := ((stieltjes_potential_derivative_integrable G hf).sub hWlin).sub
      (((stieltjes_deriv_integrable G a b).sub (integrable_const 1)).const_mul k)
    apply hi.congr
    filter_upwards [] with r
    simp only [Pi.sub_apply]
    ring
  have hcenter := stieltjes_first_order_centered G hab hleft hf hWlin (k:=k)
  have hcomp : (Lref+initial)+A*ds+k*(G b-b)+
      (∫ r in Icc a b, ((∫ t in r..b, f t)-W r-k)*(deriv G r-1))+
      (∫ r in Icc a b, W r*transportEntropy (deriv G r))+
      (∫ r in Icc a b, (∫ t in r..b, f t)-k ∂G.measure.singularPart volume)+kappa*ds^2-
      Krank*((∫ r in Icc a b, transportVariationDensity (deriv G r))+
        ((G.measure.singularPart volume).restrict (Icc a b)).real univ) ≤ Lambda := by
    rw [measureReal_restrict_apply_univ]
    unfold matchingVariation at hflowTaylor
    linarith only [hcenter,hflowTaylor]
  have hh := reference_transport_coercivity hW0 hk (sub_nonpos.mpr hend) hW
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr; exact ha r hr) hxi
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr; linarith [ha r hr])
    (stieltjes_variation_integrable G a b) herr hlin hent hPnu heps hkappa hA hcomp
  simpa only [matchingVariation,measureReal_restrict_apply_univ] using hh

end OptimalG.Variational
