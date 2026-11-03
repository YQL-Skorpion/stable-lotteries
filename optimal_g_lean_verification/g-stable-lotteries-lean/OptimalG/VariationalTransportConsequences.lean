import OptimalG.VariationalTransportIntegral
import OptimalG.VariationalTransportDeficit

/-! Exclusion and localization consequences of the checked transport
comparison. They retain both scalar slack and rank variation when required. -/
namespace OptimalG.Variational
open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

 theorem reference_transport_coercivity_retaining_slack {mu nu : Measure X} [IsFiniteMeasure nu]
    {P W xi : X → ℝ} {W0 k A A0 kappa keep ds eb Krank eps Lref Lambda : ℝ}
    (hW0 : 0 ≤ W0) (hk : k ≤ 0) (heb : eb ≤ 0)
    (hW : ∀ᵐ r ∂mu, W0 ≤ W r) (ha : ∀ᵐ r ∂mu, 0 < P r-k-W0)
    (hxi : ∀ᵐ r ∂mu, 0 < xi r)
    (hnu : ∀ᵐ r ∂nu, W0 ≤ P r-k)
    (hvar : Integrable (fun r => transportVariationDensity (xi r)) mu)
    (herr : Integrable (fun r => (P r-W r-k)^2/(P r-k-W0)) mu)
    (hlin : Integrable (fun r => (P r-W r-k)*(xi r-1)) mu)
    (hent : Integrable (fun r => W r*transportEntropy (xi r)) mu)
    (hP : Integrable (fun r => P r-k) nu)
    (heps : (∫ r, (P r-W r-k)^2/(P r-k-W0) ∂mu) ≤ eps)
    (hkappa : keep < kappa) (hA : |A| ≤ A0)
    (hcomparison : Lref+A*ds+k*eb+
      (∫ r, (P r-W r-k)*(xi r-1) ∂mu)+(∫ r, W r*transportEntropy (xi r) ∂mu)+
      (∫ r, P r-k ∂nu)+kappa*ds^2-
      Krank*((∫ r, transportVariationDensity (xi r) ∂mu)+nu.real univ) ≤ Lambda) :
    Lref-eps-A0^2/(4*(kappa-keep))+keep*ds^2+((8:ℝ)/9*W0-Krank)*
      ((∫ r, transportVariationDensity (xi r) ∂mu)+nu.real univ) ≤ Lambda := by
  have hcomparison' : (Lref+keep*ds^2)+A*ds+k*eb+
      (∫ r, (P r-W r-k)*(xi r-1) ∂mu)+(∫ r, W r*transportEntropy (xi r) ∂mu)+
      (∫ r, P r-k ∂nu)+(kappa-keep)*ds^2-
      Krank*((∫ r, transportVariationDensity (xi r) ∂mu)+nu.real univ) ≤ Lambda := by
    nlinarith only [hcomparison]
  have hh := reference_transport_coercivity hW0 hk heb hW ha hxi hnu hvar herr hlin hent hP heps
    (sub_pos.mpr hkappa) hA hcomparison'
  nlinarith only [hh]

 theorem transport_exclusion {base gap V Lambda : ℝ}
    (hbase : 0 < base) (hgap : 0 ≤ gap) (hV : 0 ≤ V)
    (hcomparison : base+gap*V ≤ Lambda) (hfeasible : Lambda ≤ 0) : False := by
  have h := mul_nonneg hgap hV
  linarith

 theorem transport_joint_localization {base keep gap ds V Lambda : ℝ}
    (hkeep : 0 < keep) (hgap : 0 < gap) (hV : 0 ≤ V)
    (hcomparison : base+keep*ds^2+gap*V ≤ Lambda) (hfeasible : Lambda ≤ 0) :
    ds^2 ≤ -base/keep ∧ V ≤ -base/gap := by
  constructor
  · apply (le_div_iff₀ hkeep).2
    have h := mul_nonneg hgap.le hV
    nlinarith only [h,hcomparison,hfeasible]
  · apply (le_div_iff₀ hgap).2
    have h := mul_nonneg hkeep.le (sq_nonneg ds)
    nlinarith only [h,hcomparison,hfeasible]

end OptimalG.Variational
