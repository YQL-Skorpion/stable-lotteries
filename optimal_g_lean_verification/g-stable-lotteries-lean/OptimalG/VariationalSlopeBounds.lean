import OptimalG.VariationalLowSlope
import OptimalG.VariationalHeadBounds

/-! Exact scalar slope bounds used to compare the cap, affine head and
free minimizing segment. Only the head/free ordering needs the finer S tube. -/
namespace OptimalG.Variational
open Set

 theorem Admissible.capScore_curvature_lower {lam r : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hr : r ≤ xHi) :
    -(0.126 : ℝ) ≤ -2*lam*d.S/(1-r)^3 := by
  have hL := hd.compact_lambdaRange
  have hS := hd.slack_upper
  have hS0 : 0 ≤ d.S := by linarith [hd.slack_lower]
  have hr' : r ≤ (0.38 : ℝ) := by convert! hr using 1 <;> norm_num [xHi]
  have hnum := mul_le_mul hL.2 hS hS0 (by norm_num : (0:ℝ) ≤ 0.562330)
  have hpow : (0.62 : ℝ)^3 ≤ (1-r)^3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  apply (le_div_iff₀ (pow_pos (by linarith : 0 < 1-r) 3)).mpr
  nlinarith only [hnum,hpow]

 theorem Admissible.capScore_lower_increment_uniform {lam r s : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hrs : r ≤ s) (hs : s ≤ xHi) :
    capScore lam d.S r-(0.126 : ℝ)*(s-r) ≤ capScore lam d.S s := by
  have hh := reference_primitive_lower_increment (a:=r) (b:=s) (m0:= -(0.126 : ℝ))
    (fun t ht => capScore_hasDerivAt lam d.S t
      (ne_of_lt ((ht.2.trans hs).trans_lt (by norm_num [xHi]))))
    (fun t ht => hd.capScore_curvature_lower (ht.2.le.trans hs))
    r ⟨le_rfl,hrs⟩ s ⟨hrs,le_rfl⟩ hrs
  linarith

 theorem Admissible.headSlope_gt_tube {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hS : (0.02271790 : ℝ) ≤ d.S) :
    -(0.691 : ℝ) < headSlope (0.2635 : ℝ) (cap lam d.S 0.2635) (capScore lam d.S 0.2635) := by
  have hL := hd.compact_lambdaRange
  have hL0 : 0 ≤ lam := by linarith [hL.1]
  have hLS := mul_le_mul hL.1 hS (by norm_num : (0:ℝ) ≤ 0.02271790) hL0
  have hLsq : lam^2 ≤ (0.562330 : ℝ)^2 := pow_le_pow_left₀ hL0 hL.2 2
  simp only [headSlope,headInitial,cap,capScore]
  norm_num
  nlinarith only [hL.1,hL.2,hLS,hLsq]

 theorem Admissible.free_slope_le_head_of_tube {lam theta : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hS : (0.02271790 : ℝ) ≤ d.S) (htheta : (0.691 : ℝ) ≤ theta) :
    -theta ≤ headSlope (0.2635 : ℝ) (cap lam d.S 0.2635) (capScore lam d.S 0.2635) := by
  linarith [hd.headSlope_gt_tube hS]

end OptimalG.Variational
