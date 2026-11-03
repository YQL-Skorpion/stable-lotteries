import OptimalG.VariationalTransportWeights

/-! A reference exclusion needs only a positive net scalar budget. The
reference parameter, mesh sizes, and numerical tolerances are absent from
this criterion; concrete certificates supply its explicit bounds. -/
namespace OptimalG.Certificates.Transport

theorem lower_reference_budget_lower_bound
    {Lref A Amax ds kappa k other eps : ℝ}
    (hk : 0 < k) (hkap : k ≤ kappa) (hA : |A| ≤ Amax) (ho : 0 ≤ other) :
    Lref - eps - Amax ^ 2 / (4 * k) ≤
      Lref + A * ds + kappa * ds ^ 2 + other - eps := by
  have hsq := Variational.slack_square_completion (s := ds) hk hA
  have hmore := mul_le_mul_of_nonneg_right hkap (sq_nonneg ds)
  linarith only [hsq, hmore, ho]

/-- A strictly positive net reference budget excludes every scalar
perturbation, with its actual signed linear coefficient. -/
theorem lower_reference_budget_excludes_general
    {Lref A Amax ds kappa k other eps : ℝ}
    (hk : 0 < k) (hkap : k ≤ kappa) (hA : |A| ≤ Amax) (ho : 0 ≤ other)
    (hgap : Amax ^ 2 / (4 * k) < Lref - eps)
    (htransport : Lref + A * ds + kappa * ds ^ 2 + other ≤ eps) : False := by
  have h := lower_reference_budget_lower_bound (Lref := Lref) (ds := ds)
    (eps := eps) hk hkap hA ho
  linarith only [h, hgap, htransport]

/-- The same criterion in terms of independently certified lower/upper
endpoint constants. No proposed constant is presumed correct. -/
theorem lower_reference_budget_excludes_of_bounds
    {Lref Lmin A Amax ds kappa k other eps Emax : ℝ}
    (hk : 0 < k) (hkap : k ≤ kappa) (hA : |A| ≤ Amax) (ho : 0 ≤ other)
    (hL : Lmin ≤ Lref) (heps : eps ≤ Emax)
    (hgap : Amax ^ 2 / (4 * k) < Lmin - Emax)
    (htransport : Lref + A * ds + kappa * ds ^ 2 + other ≤ eps) : False := by
  apply lower_reference_budget_excludes_general hk hkap hA ho ?_ htransport
  linarith only [hL, heps, hgap]

end OptimalG.Certificates.Transport
