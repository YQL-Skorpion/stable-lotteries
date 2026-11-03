import OptimalG.Certificates.Control
import OptimalG.Certificates.GeneratedControl

/-! Exact coupled control coefficient bounds on the full admissible rectangle. -/

namespace OptimalG.Certificates.Control

private theorem vec4_two (a b c d : ℝ) : (![a,b,c,d] : Fin 4 → ℝ) 2 = c := rfl
private theorem vec4_three (a b c d : ℝ) : (![a,b,c,d] : Fin 4 → ℝ) 3 = d := rfl

theorem ratio_margin_positive (L S p U : ℝ)
    (hL : Compact.LambdaRange L) (hS : Compact.ScalarRange S)
    (hp : p ∈ Set.Icc (0.25 : ℝ) 0.36)
    (hU : U ∈ Set.Icc (0.21267 : ℝ) 0.313) :
    0 < U * (quadratic L (1-p)-S) * (0.74*(1-p)-L) +
      p*(U-p/2)*(1-p)*(0.74*(2*L-0.38)-(p+0.38-L)) := by
  have hb : ∀ i, (GeneratedControl.domain i).Contains (![L,S,p,U] i) := by
    intro i
    fin_cases i <;>
      norm_num [GeneratedControl.domain, RatInterval.Contains,
        Compact.LambdaRange, Compact.ScalarRange, Compact.scalarLower,
        Compact.scalarUpper, vec4_two, vec4_three] at hL hS hp hU ⊢ <;> assumption
  have hr := BoxCertificate.checkLower_sound _ _ _ _ GeneratedControl.checked _ hb
  norm_num [GeneratedControl.ratioExpr, RatExpr.eval, vec4_two, vec4_three] at hr
  unfold quadratic
  nlinarith [hr]

/-- The coupled estimate uses the primitive cap and the state ceiling;
independent interval ranges for R and K would lose this inequality. -/
theorem coefficient_ratio (L S p U x y R K : ℝ)
    (hL : Compact.LambdaRange L) (hS : Compact.ScalarRange S)
    (hp : p ∈ Set.Icc (0.25 : ℝ) 0.36)
    (hU : U ∈ Set.Icc (0.21267 : ℝ) 0.313)
    (hx : x ≤ 0.38) (hy : y ≤ 0.38)
    (hR : (1-p)*R ≤ L*(quadratic L (1-p)-S))
    (hK : p*(U-p/2) ≤ K) :
    cx U (p+y-L) R K < 0.74 * cy U (2*L-x) (quadratic L (1-p)-S) K := by
  have hq : 0 < 1-p := by linarith [hp.2]
  have hU0 : 0 ≤ U := by linarith [hU.1]
  have hK0 : 0 ≤ p*(U-p/2) :=
    mul_nonneg (by linarith [hp.1]) (by linarith [hU.1, hp.2])
  have hc : 0 < 0.74*(2*L-0.38)-(p+0.38-L) := by
    linarith [hL.1, hp.2]
  have hc' : 0.74*(2*L-0.38)-(p+0.38-L) ≤ 0.74*(2*L-x)-(p+y-L) := by
    linarith
  have hkp := mul_le_mul hK hc' (le_of_lt hc) (hK0.trans hK)
  have hkq := mul_le_mul_of_nonneg_right hkp (le_of_lt hq)
  have hr := mul_le_mul_of_nonneg_left hR hU0
  have hm := ratio_margin_positive L S p U hL hS hp hU
  have hd : 0 < (1-p)*(0.74*cy U (2*L-x) (quadratic L (1-p)-S) K -
      cx U (p+y-L) R K) := by
    unfold cx cy
    nlinarith [hkq, hr, hm]
  have := (mul_pos_iff_of_pos_left hq).mp hd
  linarith

theorem ratio_below_binary (L p : ℝ) (hL : Compact.LambdaRange L)
    (hp : p ∈ Set.Icc (0.25 : ℝ) 0.36) :
    (0.74 : ℝ) < L/(1-p) := by
  apply (lt_div_iff₀ (show 0 < 1-p by linarith [hp.2])).mpr
  linarith [hp.1, hL.1]

end OptimalG.Certificates.Control
