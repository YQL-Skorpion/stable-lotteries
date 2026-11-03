import OptimalG.VariationalStieltjesCoercivity
import OptimalG.VariationalTransportIntegrability

/-! The integrability premises of Stieltjes coercivity follow from the same
finite weight and potential bounds used by the flux certificates. Singular
matching remains allowed; only its almost-everywhere derivative is integrated
against Lebesgue measure. -/
namespace OptimalG.Variational
open Set MeasureTheory Real

 theorem stieltjes_weighted_integrability (G : StieltjesFunction ℝ) {a b delta B : ℝ}
    {W : ℝ→ℝ} (hW : AEStronglyMeasurable W (volume.restrict (Icc a b)))
    (hbound : ∀ᵐ r ∂volume.restrict (Icc a b),|W r|≤B)
    (hdelta : 0<delta)
    (hlower : ∀ᵐ r ∂volume.restrict (Icc a b),delta≤deriv G r) :
    IntegrableOn (fun r=>W r*(deriv G r-1)) (Icc a b) ∧
      IntegrableOn (fun r=>W r*transportEntropy (deriv G r)) (Icc a b) := by
  have hb : ∀ᵐ r ∂volume.restrict (Icc a b),‖W r‖≤B := by
    simpa only [Real.norm_eq_abs] using hbound
  exact ⟨((stieltjes_deriv_integrable G a b).sub (integrable_const 1)).bdd_mul hW hb,
    (transportEntropy_integrable (stieltjes_deriv_integrable G a b) hdelta hlower).bdd_mul hW hb⟩

 theorem bounded_transport_error_integrable {X : Type*} [MeasurableSpace X]
    {mu : Measure X} [IsFiniteMeasure mu] {P W : X→ℝ} {BP BW delta k W0 : ℝ}
    (hP : AEStronglyMeasurable P mu) (hW : AEStronglyMeasurable W mu)
    (hBP : 0≤BP) (hBW : 0≤BW) (hdelta : 0<delta)
    (hPb : ∀ᵐ r ∂mu,|P r|≤BP) (hWb : ∀ᵐ r ∂mu,|W r|≤BW)
    (hden : ∀ᵐ r ∂mu,delta≤P r-k-W0) :
    Integrable (fun r=>(P r-W r-k)^2/(P r-k-W0)) mu := by
  have hm : AEStronglyMeasurable (fun r=>(P r-W r-k)^2/(P r-k-W0)) mu :=
    ((((hP.aemeasurable.sub hW.aemeasurable).sub aemeasurable_const).pow_const 2).div
      ((hP.aemeasurable.sub aemeasurable_const).sub aemeasurable_const)).aestronglyMeasurable
  apply (integrable_const ((BP+BW+|k|)^2/delta)).mono' hm
  filter_upwards [hPb,hWb,hden] with r hp hw hd
  have hdpos : 0<P r-k-W0 := hdelta.trans_le hd
  have habs : |P r-W r-k|≤BP+BW+|k| := by
    calc
      _≤|P r-W r|+|k| := abs_sub _ _
      _≤(|P r|+|W r|)+|k| := by linarith only [abs_sub (P r) (W r)]
      _≤BP+BW+|k| := by linarith
  have hsq : (P r-W r-k)^2≤(BP+BW+|k|)^2 := by
    nlinarith only [habs,abs_nonneg (P r-W r-k),sq_abs (P r-W r-k)]
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) hdpos.le)]
  exact (div_le_div_of_nonneg_right hsq hdpos.le).trans
    (div_le_div_of_nonneg_left (sq_nonneg _) hdelta hd)

end OptimalG.Variational
