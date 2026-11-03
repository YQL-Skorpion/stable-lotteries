import OptimalG.VariationalLowCurve
import OptimalG.PolynomialCompletion

/-! The head completion at rank .2635 needs only the original admissible
scalar rectangle; it does not require localization of the minimizer. -/
namespace OptimalG.Variational

 theorem Admissible.head_completion_bounds {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) :
    headSlope (0.2635 : ℝ) (cap lam d.S 0.2635) (capScore lam d.S 0.2635) < 0 ∧
      headInitial (0.2635 : ℝ) (cap lam d.S 0.2635) (capScore lam d.S 0.2635) ≤ lam := by
  have hL := hd.compact_lambdaRange
  have hS := hd.slack_upper
  have hSlo := hd.slack_lower
  have hL0 : 0 ≤ lam := by linarith [hL.1]
  have hS0 : 0 ≤ d.S := by linarith
  have hLSupper := mul_le_mul hL.2 hS hS0 (by norm_num : (0:ℝ) ≤ 0.562330)
  have hLSlower := mul_le_mul hL.1 hSlo (by norm_num : (0:ℝ) ≤ 21972/1000000) hL0
  have hLsqLower : (0.562325 : ℝ)^2 ≤ lam^2 := pow_le_pow_left₀ (by norm_num) hL.1 2
  have hLsqUpper : lam^2 ≤ (0.562330 : ℝ)^2 := pow_le_pow_left₀ hL0 hL.2 2
  constructor <;> simp only [headSlope,headInitial,cap,capScore] <;> norm_num <;>
    nlinarith only [hL.1,hL.2,hLSupper,hLSlower,hLsqLower,hLsqUpper]

end OptimalG.Variational
