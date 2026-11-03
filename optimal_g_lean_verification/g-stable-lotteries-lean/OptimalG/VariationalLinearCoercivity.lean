import OptimalG.VariationalBoundaryCoercivity

/-! Full transport coercivity retaining the terminal matching displacement,
scalar slack square, initial high-deficit term and singular matching mass. -/
namespace OptimalG.Variational
open Set MeasureTheory Function

variable {X : Type*} [MeasurableSpace X]

theorem reference_transport_coercivity_linear {mu nu : Measure X} [IsFiniteMeasure nu]
    {P W xi : X → ℝ} {W0 k A kappa ds eb Krank eps Lref Lambda : ℝ}
    (hW0 : 0 ≤ W0)
    (hW : ∀ᵐ r ∂mu, W0 ≤ W r) (ha : ∀ᵐ r ∂mu, 0 < P r-k-W0)
    (hxi : ∀ᵐ r ∂mu, 0 < xi r)
    (hnu : ∀ᵐ r ∂nu, W0 ≤ P r-k)
    (hvar : Integrable (fun r => transportVariationDensity (xi r)) mu)
    (herr : Integrable (fun r => (P r-W r-k)^2/(P r-k-W0)) mu)
    (hlin : Integrable (fun r => (P r-W r-k)*(xi r-1)) mu)
    (hent : Integrable (fun r => W r*transportEntropy (xi r)) mu)
    (hP : Integrable (fun r => P r-k) nu)
    (heps : (∫ r, (P r-W r-k)^2/(P r-k-W0) ∂mu) ≤ eps)
    (hcomparison : Lref+A*ds+k*eb+
      (∫ r, (P r-W r-k)*(xi r-1) ∂mu)+(∫ r, W r*transportEntropy (xi r) ∂mu)+
      (∫ r, P r-k ∂nu)+kappa*ds^2-
      Krank*((∫ r, transportVariationDensity (xi r) ∂mu)+nu.real univ) ≤ Lambda) :
    Lref-eps+A*ds+kappa*ds^2+k*eb+((8:ℝ)/9*W0-Krank)*
      ((∫ r, transportVariationDensity (xi r) ∂mu)+nu.real univ) ≤ Lambda := by
  have hac := transport_integral_coercivity hW0 hW ha hxi hvar herr hlin hent
  have hsing := transport_singular_coercivity hnu hP
  have hmass : 0 ≤ nu.real univ := measureReal_nonneg
  have hsingextra : 0 ≤ ((1:ℝ)/9*W0)*nu.real univ := mul_nonneg (by positivity) hmass
  nlinarith only [hac,hsing,hsingextra,heps,hcomparison]

theorem stieltjes_reference_coercivity_linear (G : StieltjesFunction ℝ) {a b : ℝ}
    (hab : a ≤ b) (hleft : leftLim G a = a) (hend : G b ≤ b)
    {f W : ℝ → ℝ} {W0 k A kappa ds Krank eps Lref initial Lambda : ℝ}
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
    (hflowTaylor : Lref+initial+A*ds+(∫ r in Icc a b, f r*(G r-r))-
      (∫ r in Icc a b, W r*(deriv G r-1))+
      (∫ r in Icc a b, W r*transportEntropy (deriv G r))+kappa*ds^2-
      Krank*matchingVariation G a b ≤ Lambda) :
    Lref+initial-eps+A*ds+kappa*ds^2+k*(G b-b)+
      ((8:ℝ)/9*W0-Krank)*matchingVariation G a b ≤ Lambda := by
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
  have hh := reference_transport_coercivity_linear hW0 hW
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr; exact ha r hr) hxi
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr; linarith [ha r hr])
    (stieltjes_variation_integrable G a b) herr hlin hent hPnu heps hcomp
  simpa only [matchingVariation,measureReal_restrict_apply_univ] using hh


 theorem transport_scalar_radius {kappa A A0 ds budget radius : ℝ}
    (hkappa : 0 < kappa) (hA : |A| ≤ A0) (hradius : 0 ≤ radius)
    (hcenter : A0 ≤ 2*kappa*radius)
    (hgap : budget < kappa*radius^2-A0*radius)
    (hbound : kappa*ds^2+A*ds ≤ budget) : |ds| < radius := by
  have hA0 : 0 ≤ A0 := (abs_nonneg A).trans hA
  have hm := mul_le_mul_of_nonneg_right hA (abs_nonneg ds)
  have hneg := neg_abs_le (A*ds)
  rw [abs_mul] at hneg
  have hsq : |ds|^2=ds^2 := sq_abs ds
  have hsqk := congrArg (fun q : ℝ => kappa*q) hsq
  by_contra hn
  have hlarge : radius ≤ |ds| := le_of_not_gt hn
  have hsum : 0 ≤ kappa*(|ds|+radius)-A0 := by
    have hi := mul_le_mul_of_nonneg_left hlarge hkappa.le
    linarith
  have hp := mul_nonneg (sub_nonneg.mpr hlarge) hsum
  nlinarith only [hbound,hm,hneg,hsqk,hgap,hp]

 theorem transport_auxiliary_budget {initial kappa A A0 ds k eb gap V budget : ℝ}
    (hkappa : 0 < kappa) (hA : |A| ≤ A0)
    (hbound : initial+A*ds+kappa*ds^2+k*eb+gap*V ≤ budget) :
    initial+k*eb+gap*V ≤ budget+A0^2/(4*kappa) := by
  have hh := slack_square_completion hkappa hA (s:=ds)
  linarith

end OptimalG.Variational
