import OptimalG.VariationalTransportIntegral

/-! Cauchy--Schwarz for the actual absolutely continuous and singular
transport contributions, proved directly by integrating a square. -/
namespace OptimalG.Variational
open MeasureTheory Set

 theorem transport_young {x t : ℝ} (hx : 0 < x) :
    2*t*(x-1) ≤ transportVariationDensity x+t^2*(x+1) := by
  have hden : 0 < x+1 := by linarith
  have hs := div_nonneg (sq_nonneg ((x-1)-t*(x+1))) hden.le
  have he : transportVariationDensity x+t^2*(x+1)-2*t*(x-1) =
      ((x-1)-t*(x+1))^2/(x+1) := by
    unfold transportVariationDensity
    field_simp
    ring
  linarith

variable {X : Type*} [MeasurableSpace X]

 theorem transport_displacement_young {mu : Measure X} [IsFiniteMeasure mu]
    {xi : X → ℝ} {sigma t : ℝ}
    (hxi : Integrable xi mu) (hpos : ∀ᵐ r ∂mu, 0 < xi r)
    (hvar : Integrable (fun r => transportVariationDensity (xi r)) mu)
    (hsigma : 0 ≤ sigma) :
    2*t*((∫ r, xi r-1 ∂mu)+sigma) ≤
      ((∫ r, transportVariationDensity (xi r) ∂mu)+sigma)+
      t^2*((∫ r, xi r+1 ∂mu)+sigma) := by
  have hi1 : Integrable (fun r => xi r-1) mu := hxi.sub (integrable_const 1)
  have hi2 : Integrable (fun r => xi r+1) mu := hxi.add (integrable_const 1)
  have h := integral_mono_ae (hi1.const_mul (2*t)) (hvar.add (hi2.const_mul (t^2)))
    (by filter_upwards [hpos] with r hr; exact transport_young (t:=t) hr)
  simp only [Pi.sub_apply,Pi.add_apply] at h
  rw [integral_const_mul,integral_add hvar (hi2.const_mul _),integral_const_mul] at h
  have hs := mul_nonneg (sq_nonneg (t-1)) hsigma
  nlinarith only [h,hs]

 theorem transport_displacement_sq_le {mu : Measure X} [IsFiniteMeasure mu]
    {xi : X → ℝ} {sigma : ℝ}
    (hxi : Integrable xi mu) (hpos : ∀ᵐ r ∂mu, 0 < xi r)
    (hvar : Integrable (fun r => transportVariationDensity (xi r)) mu)
    (hsigma : 0 ≤ sigma)
    (hmass : 0 < (∫ r, xi r+1 ∂mu)+sigma) :
    ((∫ r, xi r-1 ∂mu)+sigma)^2 ≤
      ((∫ r, xi r+1 ∂mu)+sigma)*
      ((∫ r, transportVariationDensity (xi r) ∂mu)+sigma) := by
  let e := (∫ r, xi r-1 ∂mu)+sigma
  let m := (∫ r, xi r+1 ∂mu)+sigma
  let V := (∫ r, transportVariationDensity (xi r) ∂mu)+sigma
  have h := transport_displacement_young hxi hpos hvar hsigma (t:=e/m)
  change 2*(e/m)*e ≤ V+(e/m)^2*m at h
  have hm : 0 < m := hmass
  have hh := mul_le_mul_of_nonneg_right h hm.le
  have he : 2*(e/m)*e*m-(e/m)^2*m*m = e^2 := by
    field_simp
    ring
  change e^2 ≤ m*V
  nlinarith only [hh,he]

/-- The same Cauchy estimate also covers a degenerate interval carrying no
mass. The zero-mass case is proved directly, rather than dividing by zero. -/
theorem transport_displacement_sq_le_all {mu : Measure X} [IsFiniteMeasure mu]
    {xi : X → ℝ} {sigma : ℝ}
    (hxi : Integrable xi mu) (hpos : ∀ᵐ r ∂mu, 0 < xi r)
    (hvar : Integrable (fun r => transportVariationDensity (xi r)) mu)
    (hsigma : 0 ≤ sigma) :
    ((∫ r, xi r-1 ∂mu)+sigma)^2 ≤
      ((∫ r, xi r+1 ∂mu)+sigma)*
      ((∫ r, transportVariationDensity (xi r) ∂mu)+sigma) := by
  have hbase : 0 ≤ ∫ r, xi r ∂mu := integral_nonneg_of_ae (hpos.mono (fun _ h => h.le))
  have hvolume : 0 ≤ mu.real univ := measureReal_nonneg
  have hp : (∫ r, xi r+1 ∂mu) = (∫ r, xi r ∂mu)+mu.real univ := by
    rw [integral_add hxi (integrable_const 1),integral_const]
    simp
  have hm : (∫ r, xi r-1 ∂mu) = (∫ r, xi r ∂mu)-mu.real univ := by
    rw [integral_sub hxi (integrable_const 1),integral_const]
    simp
  by_cases hmass : 0 < (∫ r, xi r+1 ∂mu)+sigma
  · exact transport_displacement_sq_le hxi hpos hvar hsigma hmass
  · have hzero : (∫ r, xi r+1 ∂mu)+sigma = 0 := by rw [hp] at *; linarith
    have he : (∫ r, xi r-1 ∂mu)+sigma = 0 := by rw [hm]; rw [hp] at hzero; linarith
    rw [he,hzero]
    simp

/-- A total variation-mass bound gives the displacement estimate in B.4.
The singular mass includes the initial jump, so no endpoint loss occurs. -/
 theorem transport_displacement_localization {mu : Measure X} [IsFiniteMeasure mu]
    {xi : X → ℝ} {sigma length : ℝ}
    (hxi : Integrable xi mu) (hpos : ∀ᵐ r ∂mu, 0 < xi r)
    (hvar : Integrable (fun r => transportVariationDensity (xi r)) mu)
    (hsigma : 0 ≤ sigma)
    (hmass : 0 < (∫ r, xi r+1 ∂mu)+sigma)
    (hupper : (∫ r, xi r+1 ∂mu)+sigma ≤ 2*length) :
    ((∫ r, xi r-1 ∂mu)+sigma)^2 ≤
      2*length*((∫ r, transportVariationDensity (xi r) ∂mu)+sigma) := by
  have hv : 0 ≤ (∫ r, transportVariationDensity (xi r) ∂mu)+sigma := by
    have h : 0 ≤ ∫ r, transportVariationDensity (xi r) ∂mu := integral_nonneg_of_ae (by
      filter_upwards [hpos] with r hr
      exact div_nonneg (sq_nonneg (xi r-1)) (by linarith : 0 ≤ xi r+1))
    exact add_nonneg h hsigma
  exact (transport_displacement_sq_le hxi hpos hvar hsigma hmass).trans
    (mul_le_mul_of_nonneg_right hupper hv)

end OptimalG.Variational
