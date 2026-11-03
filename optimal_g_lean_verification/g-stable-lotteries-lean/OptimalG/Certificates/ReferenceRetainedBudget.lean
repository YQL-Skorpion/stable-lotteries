import OptimalG.Certificates.ReferenceBudgetGeneral

/-! The retained lower-reference inequality has three additional nonnegative
terms: the initial deficit, an endpoint flux, and a rank-variation term.
This arithmetic bridge keeps every numerical budget explicit. -/
namespace OptimalG.Certificates.Transport

/-- A lower reference excludes all scalar/rank perturbations once the
certified net violation exceeds the scalar square-completion loss. -/
theorem retained_lower_reference_excludes
    {Lref Lmin initial A Amax ds kappa k flux endpoint gap variation eps Emax : ℝ}
    (hk : 0 < k) (hkap : k ≤ kappa) (hA : |A| ≤ Amax)
    (hinitial : 0 ≤ initial) (hflux : flux ≤ 0) (hend : endpoint ≤ 0)
    (hrank : 0 ≤ gap) (hvariation : 0 ≤ variation)
    (hL : Lmin ≤ Lref) (heps : eps ≤ Emax)
    (hbudget : Amax ^ 2 / (4 * k) < Lmin - Emax)
    (htransport : Lref + initial - eps + A * ds + kappa * ds ^ 2 +
      flux * endpoint + gap * variation ≤ 0) : False := by
  have ho : 0 ≤ initial + flux * endpoint + gap * variation :=
    add_nonneg (add_nonneg hinitial (mul_nonneg_of_nonpos_of_nonpos hflux hend))
      (mul_nonneg hrank hvariation)
  apply lower_reference_budget_excludes_of_bounds (ds := ds) hk hkap hA ho hL heps hbudget
  linarith only [htransport]

/-- The clean coarse-reference targets imply exclusion. The targets remain
explicit premises; this is only their exact arithmetic combination. -/
theorem retained_coarse_lower_reference_excludes
    {Lref initial A ds kappa flux endpoint gap variation eps : ℝ}
    (hL : (1/2500:ℝ) ≤ Lref) (hA : |A| ≤ (1/20:ℝ))
    (hkap : (30:ℝ) ≤ kappa) (heps : eps ≤ (1/10000:ℝ))
    (hinitial : 0 ≤ initial) (hflux : flux ≤ 0) (hend : endpoint ≤ 0)
    (hrank : 0 ≤ gap) (hvariation : 0 ≤ variation)
    (htransport : Lref + initial - eps + A * ds + kappa * ds ^ 2 +
      flux * endpoint + gap * variation ≤ 0) : False := by
  exact retained_lower_reference_excludes (by norm_num : (0:ℝ)<30) hkap hA
    hinitial hflux hend hrank hvariation hL heps (by norm_num) htransport

end OptimalG.Certificates.Transport
