import OptimalG.RelocationRegularity
import OptimalG.PhasePropagation

/-! Actual terminal-obstacle change under both slack-removal phases. -/
namespace OptimalG.Relocation
open Set Variational

theorem second_terminal_obstacle_bound {lam : ℝ} {phi : ℝ → ℝ}
    (h : NormalizedNecessaryTwoClass lam phi) (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {z q : ℝ}
    (hz : z ∈ Icc zTest zEnd) (hq : q ∈ Icc qLo qHi) :
    z*(secondPrimitive lam phi (1-z+q)-secondPrimitive lam phi q)/(lam-q) ≤
      z*(activationPrimitive phi (1-z+q)-activationPrimitive phi q)/(lam-q)+3.1*massOne lam phi := by
  have hz' : z ∈ Icc (0.84 : ℝ) 0.875 := by convert hz using 1 <;> norm_num [zTest,zEnd]
  have hq' : q ∈ Icc (0.26 : ℝ) 0.28 := by convert hq using 1 <;> norm_num [qLo,qHi]
  have hr : 1-z+q ∈ Icc (0.385 : ℝ) 0.44 := ⟨by linarith [hz'.2,hq'.1],by linarith [hz'.1,hq'.2]⟩
  have hrI : 1-z+q ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have hqI : q ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hq'.1],by linarith [hq'.2]⟩
  have hqeq : secondPrimitive lam phi q=activationPrimitive phi q+prefixGain lam phi := by
    rw [secondPrimitive,second_low_eq h hL hLP (by linarith [hq'.2]),
      first_low_eq h hL hLP ⟨by linarith [hq'.1],by linarith [hq'.2]⟩,slack_eq lam phi hqI]
    unfold cumulativeSlack
    ring
  have hre : secondPrimitive lam phi (1-z+q) ≤
      activationPrimitive phi (1-z+q)+prefixGain lam phi+massOne lam phi := by
    have hg := (first_gain_bounds h hL hLP (by linarith [hr.1] : (0.245 : ℝ) ≤ 1-z+q)).2
    rw [secondPrimitive,second_low_eq h hL hLP hr.2]
    rw [slack_eq lam phi hrI] at hg
    unfold cumulativeSlack at hg
    linarith
  have hdiff : secondPrimitive lam phi (1-z+q)-secondPrimitive lam phi q ≤
      activationPrimitive phi (1-z+q)-activationPrimitive phi q+massOne lam phi := by
    rw [hqeq]
    linarith
  have hd : 0 < lam-q := by linarith [hL.1,hq'.2]
  have hratio : z/(lam-q) ≤ (3.1 : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    linarith [hz'.2,hL.1,hq'.2]
  have hm := (mass_budget h hL hLP).1
  calc
    _ ≤ z*(activationPrimitive phi (1-z+q)-activationPrimitive phi q+massOne lam phi)/(lam-q) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff (by linarith [hz'.1])) hd.le
    _ = z*(activationPrimitive phi (1-z+q)-activationPrimitive phi q)/(lam-q)+
        (z/(lam-q))*massOne lam phi := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hratio hm)

theorem second_terminal_tests {lam : ℝ} {phi Y Z : ℝ → ℝ}
    (h : NormalizedNecessaryTwoClass lam phi) (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi)
    (hflow : ∀ z ∈ Icc zStart zEnd,
      Y z+prefixGain lam phi+0.216*(massOne lam phi+massTwo lam phi) ≤ Z z)
    (hterm : ∀ z ∈ Icc zTest zEnd, ∀ q ∈ Icc qLo qHi,
      z*(activationPrimitive phi (1-z+q)-activationPrimitive phi q)/(lam-q) ≤ Y z) :
    ∀ z ∈ Icc zTest zEnd, ∀ q ∈ Icc qLo qHi,
      z*(secondPrimitive lam phi (1-z+q)-secondPrimitive lam phi q)/(lam-q)+
        0.096*massOne lam phi+0.216*massTwo lam phi ≤ Z z := by
  intro z hz q hq
  have hzfull : z ∈ Icc zStart zEnd := ⟨by norm_num [zStart,zTest] at *; linarith [hz.1],hz.2⟩
  have hh := second_terminal_obstacle_bound h hL hLP hz hq
  have hf := hflow z hzfull
  have ht := hterm z hz q hq
  unfold prefixGain at hf
  linarith

end OptimalG.Relocation
