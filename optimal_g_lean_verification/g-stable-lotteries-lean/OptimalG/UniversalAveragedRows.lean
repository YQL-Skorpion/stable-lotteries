import OptimalG.UniversalBinAverage
import OptimalG.NecessaryThreeClass
import OptimalG.UniversalLPRow

/-! # Actual bin averages of the election inequalities

These inequalities are obtained by integrating the necessary finite-election
tests. No averaged election inequality is a premise.
-/
namespace OptimalG
open Set MeasureTheory

namespace NormalizedNecessaryTwoClass
variable {L : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass L phi)
include h

theorem primitive_binAverage {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    binAverage (activationPrimitive phi) a b =
      (primitiveMoment phi b - primitiveMoment phi a) / (b - a) := by
  rw [binAverage, ← h.moment_increment ha hab.le hb]

theorem activation_binAverage {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    binAverage phi a b = (activationPrimitive phi b - activationPrimitive phi a) / (b - a) := by
  rw [binAverage, ← h.primitive_increment ha hab.le hb]

theorem shifted_primitive_binAverage {a b d : ℝ} (ha : 0 ≤ d + a)
    (hab : a < b) (hb : d + b ≤ 1) :
    binAverage (fun r => activationPrimitive phi (d + r)) a b =
      (primitiveMoment phi (d + b) - primitiveMoment phi (d + a)) / (b - a) := by
  rw [binAverage, intervalIntegral.integral_comp_add_left]
  rw [← h.moment_increment ha (by linarith) hb]

/-- The binary-integral LP row, for an arbitrary nondegenerate q-bin. -/
theorem two_class_bin_integral (hL0 : 0 < L) (hL1 : L < 1)
    {p a b : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (ha : 0 ≤ a)
    (hab : a < b) (hbp : b ≤ p) (hbL : b ≤ L) :
    p * ((primitiveMoment phi (1 - p + b) - primitiveMoment phi (1 - p + a) -
      (primitiveMoment phi b - primitiveMoment phi a)) / (b - a)) ≤
      (L - (a + b) / 2) * activationPrimitive phi p := by
  have hb1 : b ≤ 1 := hbp.trans hp.2.le
  have hc : ContinuousOn (activationPrimitive phi) (Icc a b) :=
    h.primitive_continuous.mono (Icc_subset_Icc ha hb1)
  have hcs : ContinuousOn (fun q => activationPrimitive phi (1 - p + q)) (Icc a b) := by
    apply h.primitive_continuous.comp (continuous_const.add continuous_id).continuousOn
    intro q hq
    change 0 ≤ 1 - p + q ∧ 1 - p + q ≤ 1
    constructor <;> linarith [hq.1, hq.2, hp.2]
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) hab.le
  have his := hcs.intervalIntegrable_of_Icc (μ := volume) hab.le
  have hiId : IntervalIntegrable (fun q : ℝ => q) volume a b := continuous_id.intervalIntegrable a b
  have hlin : IntervalIntegrable (fun q : ℝ => L - q) volume a b :=
    (continuous_const.sub continuous_id).intervalIntegrable a b
  have hh := binAverage_mono hab ((his.sub hi).const_mul p)
    (hlin.mul_const (activationPrimitive phi p)) (fun q hq =>
      h.two_class_all hL0 hL1 p q hp (ha.trans hq.1) (hq.2.trans hbp) (hq.2.trans hbL))
  rw [binAverage_const_mul, binAverage_sub his hi, binAverage_mul_const,
    binAverage_sub (f := fun _ => L) intervalIntegrable_const hiId,
    binAverage_const L hab, binAverage_id hab,
    h.shifted_primitive_binAverage (by linarith [hp.2]) hab (by linarith),
    h.primitive_binAverage ha hab hb1] at hh
  simpa only [← sub_div] using hh

end NormalizedNecessaryTwoClass
end OptimalG
