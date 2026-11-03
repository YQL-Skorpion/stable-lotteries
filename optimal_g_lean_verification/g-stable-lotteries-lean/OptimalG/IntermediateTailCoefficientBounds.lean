import OptimalG.Certificates.IntermediateTailExpressions

/-! Coarse exact scalar bounds discharge the sign prerequisites of the
intermediate tail comparison without an extra numerical certificate. -/
namespace OptimalG
open Set Variational Certificates.IntermediateTailExpressions

theorem intermediate_tail_coefficient_signs {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc lam (13/20:ℝ)) :
    0<Certificates.IntermediateTailExpressions.headScore lam S ∧ 0<etaNumerator lam S p := by
  have hL0 : 0≤lam := by linarith only [hL.1]
  have hp0 : 0≤p := hL0.trans hp.1
  have hS0 : 0≤S := by linarith only [hS.1]
  have hLS := mul_le_mul hL.2 hS.2 hS0 (by norm_num : (0:ℝ)≤56233/100000)
  have hF : (1/4:ℝ)≤Certificates.IntermediateTailExpressions.headScore lam S := by
    unfold Certificates.IntermediateTailExpressions.headScore capScore
    norm_num
    nlinarith only [hL.1,hLS]
  have hprod := mul_nonneg (sub_nonneg.mpr hp.2)
    (show 0≤(p+13/20)/2-lam by linarith only [hp.1,hL.2])
  have hR : (13/100:ℝ)≤massPrimitive lam S p := by
    unfold massPrimitive quadratic
    nlinarith only [hprod,hL.1,hS.2]
  have hsquare := sq_nonneg (1-p-lam)
  have hLsq := pow_le_pow_left₀ hL0 hL.2 2
  have hP : complementUpper lam S p≤(17/125:ℝ) := by
    unfold complementUpper quadratic
    nlinarith only [hsquare,hLsq,hS.1]
  have hP1 := mul_le_mul_of_nonneg_left hP hp0
  have hP2 := mul_le_mul_of_nonneg_right hp.2 (by norm_num : (0:ℝ)≤17/125)
  have hsum : (1/4+22493/40000:ℝ)≤Certificates.IntermediateTailExpressions.headScore lam S+lam := add_le_add hF hL.1
  have hgain := mul_le_mul hR hsum (by norm_num : (0:ℝ)≤1/4+22493/40000)
    (by linarith only [hR] : 0≤massPrimitive lam S p)
  refine ⟨by linarith only [hF],?_⟩
  unfold etaNumerator massFactor
  nlinarith only [hgain,hP1,hP2]

end OptimalG
