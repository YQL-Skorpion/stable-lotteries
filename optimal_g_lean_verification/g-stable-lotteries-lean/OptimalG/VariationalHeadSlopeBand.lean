import OptimalG.VariationalSlopeBounds

/-! Coarse affine-head slope bounds valid on the whole compact box. -/
namespace OptimalG.Variational

 theorem Admissible.headSlope_upper_uniform {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) :
    headSlope (0.2635:ℝ) (cap lam d.S 0.2635) (capScore lam d.S 0.2635)< -(0.63:ℝ) := by
  have hL := hd.compact_lambdaRange
  have hS := hd.slack_upper
  have hLS := mul_le_mul hL.2 hS (by linarith [hd.slack_lower] : 0≤d.S)
    (by norm_num : (0:ℝ)≤0.562330)
  have hsq : (0.562325:ℝ)^2≤lam^2 := pow_le_pow_left₀ (by norm_num) hL.1 2
  simp only [headSlope,headInitial,cap,capScore]
  norm_num
  nlinarith only [hL.1,hL.2,hLS,hsq]

 theorem Admissible.headSlope_lower_uniform {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) :
    -(0.7:ℝ)<headSlope (0.2635:ℝ) (cap lam d.S 0.2635) (capScore lam d.S 0.2635) := by
  have hL := hd.compact_lambdaRange
  have hS := hd.slack_lower
  have hL0 : 0≤lam := by linarith [hL.1]
  have hLS := mul_le_mul hL.1 hS (by norm_num : (0:ℝ)≤21972/1000000) hL0
  have hsq : lam^2≤(0.562330:ℝ)^2 := pow_le_pow_left₀ hL0 hL.2 2
  simp only [headSlope,headInitial,cap,capScore]
  norm_num
  nlinarith only [hL.1,hL.2,hLS,hsq]

 theorem Admissible.cap_increment_ge_headSlope {lam r s : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hrs : r≤s) (hs : s≤xHi) :
    headSlope (0.2635:ℝ) (cap lam d.S 0.2635) (capScore lam d.S 0.2635)*(s-r)≤
      capScore lam d.S s-capScore lam d.S r := by
  have hh := hd.capScore_lower_increment_uniform hrs hs
  have hm := mul_le_mul_of_nonneg_right
    (show headSlope (0.2635:ℝ) (cap lam d.S 0.2635) (capScore lam d.S 0.2635)≤ -(0.126:ℝ)
      by linarith [hd.headSlope_upper_uniform]) (sub_nonneg.mpr hrs)
  linarith

end OptimalG.Variational
