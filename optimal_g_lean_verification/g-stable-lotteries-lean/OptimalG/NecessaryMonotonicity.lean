import OptimalG.NecessaryThreeClass

/-! Necessary tests persist when the distortion parameter is increased.
This permits the universal LP at lambdaHi to bound the same score at any
parameter in the compact interval, without renormalizing it. -/
namespace OptimalG
open Set

namespace NormalizedNecessaryTwoClass

theorem mono {lam L : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass lam phi)
    (hL : lam ≤ L) : NormalizedNecessaryTwoClass L phi := by
  refine ⟨h.continuous, h.integral_zero, h.endpoint, ?_, ?_⟩
  · intro r hr
    linarith [h.ceiling r hr]
  · intro p q hp hq hqp hqL hJ
    by_cases hqlam : q ≤ lam
    · have hh := h.two_class p q hp hq hqp hqlam hJ
      have hg := mul_nonneg (sub_nonneg.mpr hL) hJ.le
      nlinarith
    · have hq1 : q ≤ 1 := hqp.trans hp.2.le
      have hr : q ≤ 1 - p + q := by linarith [hp.2]
      have hr1 : 1 - p + q ≤ 1 := by linarith
      have hh := h.primitive_increment_ceiling hq hr hr1
      have hprod := mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ 1 - p by linarith [hp.2]) (show lam - q ≤ 0 by linarith)
      have hdelta : activationPrimitive phi (1 - p + q) - activationPrimitive phi q ≤ 0 := by
        nlinarith [sq_nonneg (1 - p)]
      have hleft := mul_nonpos_of_nonneg_of_nonpos hp.1.le hdelta
      have hright := mul_nonneg (sub_nonneg.mpr hqL) hJ.le
      exact hleft.trans hright

end NormalizedNecessaryTwoClass

namespace ThreeClassWeightTest

theorem parameter_increase {R P K A B C h U k d : ℝ}
    (ht : ThreeClassWeightTest R P K A B C h U k) (hd : 0 ≤ d) :
    ThreeClassWeightTest R P K A B C (h + 2 * d) (U - d) (k - d) := by
  intro w1 w2 w3 hw1 hw2 hw3 hbal href
  have hh := ht w1 w2 w3 hw1 hw2 hw3 hbal href
  have hmass := mul_nonneg hd (show 0 ≤ 2 * w1 + w2 + w3 by positivity)
  nlinarith

end ThreeClassWeightTest

namespace NormalizedNecessaryConditions

theorem mono {lam L : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryConditions lam phi)
    (hL : lam ≤ L) : NormalizedNecessaryConditions L phi := by
  refine ⟨h.toNormalizedNecessaryTwoClass.mono hL, h.primitive_pos, ?_⟩
  intro p x y z hp hx hxp hpy hy1 hpz hz1
  have hh := (h.third_class_test p x y z hp hx hxp hpy hy1 hpz hz1).parameter_increase
    (d := L - lam) (sub_nonneg.mpr hL)
  have hhx : 2 * L - x = (2 * lam - x) + 2 * (L - lam) := by ring
  have hhz : z - L = (z - lam) - (L - lam) := by ring
  have hhy : p + y - L = (p + y - lam) - (L - lam) := by ring
  rw [hhx, hhz, hhy]
  exact hh

end NormalizedNecessaryConditions
end OptimalG
