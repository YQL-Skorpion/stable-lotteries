import OptimalG.VariationalThetaUniform
import OptimalG.Certificates.ThetaUpperData

/-! The sharp supporting-slope upper bound uses only score ceilings,
the primitive lower bound, and the scalar tube upper endpoint. -/
namespace OptimalG.Variational
open Set

 theorem theta_upper_ceiling_margin {lam S p : ℝ}
    (hL : lam ∈ Icc (0.562325:ℝ) 0.562330)
    (hS : S ≤ (0.023354:ℝ)) (hp : p ∈ Icc (0.25:ℝ) 0.36) :
    0 < (0.56*lam+0.0627)*(quadratic lam p-S)+
      (0.22*max (0.285:ℝ) p-0.78*p-0.22*lam)*(quadratic lam (1-p)-S) := by
  by_cases hpe : p ≤ (0.285:ℝ)
  · rw [max_eq_left hpe]
    have hc := Certificates.ThetaUpperData.phase0_margin (p:=p) hL
      (by constructor <;> norm_num at * <;> linarith only [hp.1,hpe])
    have hm := mul_nonneg (sub_nonneg.mpr hS)
      (show 0 ≤ 0.34*lam+0.1254-0.78*p by linarith [hL.1])
    unfold quadratic
    nlinarith only [hc,hm]
  · rw [max_eq_right (le_of_not_ge hpe)]
    have hc := Certificates.ThetaUpperData.phase1_margin (p:=p) hL
      (by constructor <;> norm_num at * <;> linarith only [hp.2,hpe])
    have hm := mul_nonneg (sub_nonneg.mpr hS)
      (show 0 ≤ 0.34*lam+0.0627-0.56*p by linarith [hL.1,hp.2])
    unfold quadratic
    nlinarith only [hc,hm]

 theorem Admissible.featureTheta_lt_78 {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hS : d.S ≤ (0.023354:ℝ))
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d) :
    featureTheta lam d v < (0.78:ℝ) := by
  have hdom := (hd.controlFeatureSupport_subset hv).1
  have hp : v.1.1 ∈ Icc (0.25:ℝ) 0.36 := by
    convert! hdom.1 using 1 <;> norm_num [pLo,pHi]
  have hx : (0.285:ℝ) ≤ v.1.2.1 := by convert! hdom.2.1.1 using 1 <;> norm_num [xLo]
  have hy : max (0.285:ℝ) v.1.1 ≤ v.1.2.2 := by
    convert! hdom.2.2.1 using 1 <;> norm_num [xLo]
  have hR0 : 0 ≤ primitive lam d v.1.1 := by linarith [hd.control_R_lower hdom.1]
  have hP0 := (hd.control_P_bounds hdom.1).1
  have hRlower := hd.primitive_lower ⟨hdom.1.1,
    hdom.1.2.trans (by norm_num [pHi,zStart])⟩
  have hL := hd.compact_lambdaRange
  have hxR := mul_le_mul_of_nonneg_right
    (show 0.56*lam+0.0627 ≤ 0.56*lam+0.22*v.1.2.1 by linarith) hR0
  have hRR := mul_le_mul_of_nonneg_left hRlower
    (show 0 ≤ 0.56*lam+0.0627 by linarith [hL.1])
  have hyP := mul_le_mul_of_nonneg_right
    (show 0.22*max (0.285:ℝ) v.1.1-0.78*v.1.1-0.22*lam ≤
      0.22*v.1.2.2-0.78*v.1.1-0.22*lam by linarith) hP0
  have hmargin := theta_upper_ceiling_margin hL hS hp
  have hAx := (hd.rankScoreSupport_bounds (hd.featureSupport_rankScores hv).1).2.2
  have hBy := (hd.rankScoreSupport_bounds (hd.featureSupport_rankScores hv).2).2.2
  have hRA := mul_le_mul_of_nonneg_left hAx hR0
  have hPB := mul_le_mul_of_nonneg_left hBy hP0
  have hD : 0 < controlDeterminant lam d v.1 := by linarith [hd.determinant_positive hdom]
  unfold featureTheta Certificates.Control.theta
  change (primitive lam d v.1.1*v.2.1+(quadratic lam (1-v.1.1)-d.S)*v.2.2)/
    controlDeterminant lam d v.1 < (0.78:ℝ)
  apply (div_lt_iff₀ hD).mpr
  unfold controlDeterminant
  nlinarith only [hxR,hRR,hyP,hmargin,hRA,hPB]

end OptimalG.Variational
