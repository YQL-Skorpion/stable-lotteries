import OptimalG.VariationalTransportWeights
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Integral coercivity in the transport argument. Lebesgue and singular
contributions are kept as separate measures, including any initial atom. -/
namespace OptimalG.Variational
open MeasureTheory Set

noncomputable def transportVariationDensity (x : ℝ) : ℝ := (x-1)^2/(x+1)

variable {X : Type*} [MeasurableSpace X]

theorem transport_integral_coercivity {mu : Measure X} {P W xi : X → ℝ} {W0 k : ℝ}
    (hW0 : 0 ≤ W0)
    (hW : ∀ᵐ r ∂mu, W0 ≤ W r) (ha : ∀ᵐ r ∂mu, 0 < P r-k-W0)
    (hxi : ∀ᵐ r ∂mu, 0 < xi r)
    (hvar : Integrable (fun r => transportVariationDensity (xi r)) mu)
    (herr : Integrable (fun r => (P r-W r-k)^2/(P r-k-W0)) mu)
    (hlin : Integrable (fun r => (P r-W r-k)*(xi r-1)) mu)
    (hent : Integrable (fun r => W r*transportEntropy (xi r)) mu) :
    (8:ℝ)/9*W0*(∫ r, transportVariationDensity (xi r) ∂mu)-
      (∫ r, (P r-W r-k)^2/(P r-k-W0) ∂mu) ≤
      (∫ r, (P r-W r-k)*(xi r-1) ∂mu)+(∫ r, W r*transportEntropy (xi r) ∂mu) := by
  have hp := integral_mono_ae ((hvar.const_mul ((8:ℝ)/9*W0)).sub herr) (hlin.add hent)
    (by filter_upwards [hW,ha,hxi] with r hrW hra hrxi
        exact transport_weight_coercivity hW0 hrW hra hrxi)
  simp only [Pi.sub_apply,Pi.add_apply] at hp
  simpa only [integral_sub (hvar.const_mul _) herr,integral_const_mul,integral_add hlin hent] using hp

/-- Singular transport contributes at least its full constant weight. -/
theorem transport_singular_coercivity {nu : Measure X} [IsFiniteMeasure nu]
    {P : X → ℝ} {W0 k : ℝ}
    (ha : ∀ᵐ r ∂nu, W0 ≤ P r-k) (hP : Integrable (fun r => P r-k) nu) :
    W0*nu.real univ ≤ ∫ r, P r-k ∂nu := by
  have h := integral_mono_ae (integrable_const W0) hP ha
  simpa only [integral_const,smul_eq_mul,mul_comm] using h

/-- Equation (B.11) implies (B.12), with all analytic and numerical inputs
visible. In particular, the hypothesis `hcomparison` is the preceding
transport comparison, not an assertion of the final result. -/
theorem reference_transport_coercivity {mu nu : Measure X} [IsFiniteMeasure nu]
    {P W xi : X → ℝ} {W0 k A A0 kappa ds eb Krank eps Lref Lambda : ℝ}
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
    (hkappa : 0 < kappa) (hA : |A| ≤ A0)
    (hcomparison : Lref+A*ds+k*eb+
      (∫ r, (P r-W r-k)*(xi r-1) ∂mu)+(∫ r, W r*transportEntropy (xi r) ∂mu)+
      (∫ r, P r-k ∂nu)+kappa*ds^2-
      Krank*((∫ r, transportVariationDensity (xi r) ∂mu)+nu.real univ) ≤ Lambda) :
    Lref-eps-A0^2/(4*kappa)+((8:ℝ)/9*W0-Krank)*
      ((∫ r, transportVariationDensity (xi r) ∂mu)+nu.real univ) ≤ Lambda := by
  have hac := transport_integral_coercivity hW0 hW ha hxi hvar herr hlin hent
  have hsing := transport_singular_coercivity hnu hP
  have hquad := slack_square_completion hkappa hA (s:=ds)
  have hbound := mul_nonneg_of_nonpos_of_nonpos hk heb
  have hmass : 0 ≤ nu.real univ := measureReal_nonneg
  have hsingextra : 0 ≤ ((1:ℝ)/9*W0)*nu.real univ := mul_nonneg (by positivity) hmass
  nlinarith only [hac,hsing,hquad,hbound,hsingextra,heps,hcomparison]

/-- Quantitative localization follows whenever the remaining constant has
been enclosed and the final logarithmic feasibility residual is nonpositive. -/
theorem transport_variation_bound {gap V base Lambda : ℝ}
    (hgap : 0 < gap) (hcoerce : base+gap*V ≤ Lambda) (hfeas : Lambda ≤ 0) :
    V ≤ -base/gap := by
  apply (le_div_iff₀ hgap).2
  nlinarith

end OptimalG.Variational
