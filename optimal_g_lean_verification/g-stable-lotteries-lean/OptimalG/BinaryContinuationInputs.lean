import OptimalG.VariationalQuadraticDeficit
import OptimalG.VariationalCapControl
import OptimalG.VariationalMiddleCurve

/-! The original continuation supplies the trajectory inputs to C.3. Its
initial line is integrated exactly; its deficit follows from the explicit
parabola control test, and the backward comparison uses an actual support point. -/
namespace OptimalG.Variational
open Set MeasureTheory

theorem continuation_line_value {lam a : ℝ} {d : LowRankData} {Y : ℝ→ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (ha : a≤zEnd)
    (hline : ∀ r ∈ Icc zStart a,continuationScore lam d Y r=lam-r) :
    ∀ r ∈ Icc zStart a,Y r=quadratic lam r-d.S := by
  intro r hr
  have hi := hd.continuationScore_integral hY ⟨hr.1,hr.2.trans ha⟩
  have he : (∫ t in zStart..r,continuationScore lam d Y t)=∫ t in zStart..r,lam-t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hr.1] at ht
    exact hline t ⟨ht.1,ht.2.trans hr.2⟩
  rw [he,intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => quadratic_hasDerivAt lam t)
    ((continuous_const.sub continuous_id).intervalIntegrable zStart r)] at hi
  linarith only [hi]

/-- These are the actual continuation bounds used by `binary_all_mass`.
The only additional inequality is a numerical control residual evaluated on
an explicit parabola; no unknown continuation occurs in that residual. -/
theorem continuation_binary_head_inputs {lam : ℝ} {d : LowRankData} {Y : ℝ→ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (hline : ∀ r ∈ Icc zStart (391/500:ℝ),continuationScore lam d Y r=lam-r)
    (hcheck : ∀ r ∈ Ico (391/500:ℝ) (807/1000:ℝ),∀ v ∈ controlFeatureSupport d,
      lam-r-2*(399/500)*(r-391/500)≤
        -featureTheta lam d v*(r-lam)-featureAlpha lam d v*
          (quadratic lam (r-v.1.1)-d.S-(quadratic lam r-d.S-(399/500)*(r-391/500)^2)))
    (hsupport : ((1459/5000:ℝ),capScore lam d.S (1459/5000))∈rankScoreSupport d.phi)
    (hR : primitive lam d (29/100)=cap lam d.S (29/100)) :
    (∀ r ∈ Icc (31/40:ℝ) (807/1000:ℝ),
      quadratic lam r-d.S-Y r≤(399/500)*(max (r-391/500) 0)^2) ∧
    (∀ r ∈ Icc (807/1000:ℝ) (17/20:ℝ),
      HasDerivAt Y (vectorField lam d r (Y r)) r ∧
      vectorField lam d r (Y r)≤highAffineControl lam d.S (29/100)
        (capDiagonalTheta lam d.S (29/100) (1459/5000))
        (capDiagonalAlpha lam d.S (29/100) (1459/5000)) Y r) := by
  have hvalue := continuation_line_value hd hY
    (by norm_num [zEnd] : (391/500:ℝ)≤zEnd) hline
  have hdef := continuation_quadratic_deficit_from_line hd hY
    (by norm_num [zStart] : zStart≤(391/500:ℝ))
    (by norm_num : (391/500:ℝ)≤807/1000)
    (by norm_num [zEnd] : (807/1000:ℝ)≤zEnd)
    (by norm_num : (0:ℝ)≤399/500) hvalue hcheck
  refine ⟨?_,original_continuation_fixed_cap_control hd hY hsupport hR⟩
  intro r hr
  apply hdef r
  constructor
  · norm_num [zStart] at *
    exact hr.1
  · exact hr.2

end OptimalG.Variational
