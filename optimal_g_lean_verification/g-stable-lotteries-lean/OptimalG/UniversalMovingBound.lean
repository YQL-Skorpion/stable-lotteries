import OptimalG.UniversalMovingAverage

/-! Certified ratio lower bounds turn actual averaged Election 3 tests into
linear inequalities in primitive values. -/
namespace OptimalG
open Set MeasureTheory

namespace NormalizedNecessaryTwoClass
variable {L : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass L phi)
include h

theorem activation_binAverage_ceiling {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    binAverage phi a b ≤ L - (a + b) / 2 := by
  have hi := (h.continuous.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc (μ := volume) hab.le
  have hiId : IntervalIntegrable (fun r : ℝ => r) volume a b := continuous_id.intervalIntegrable a b
  have hh := binAverage_mono hab hi (intervalIntegrable_const.sub hiId)
    (fun r hr => h.ceiling r ⟨ha.trans hr.1, hr.2.trans hb⟩)
  rwa [binAverage_sub intervalIntegrable_const hiId, binAverage_const L hab, binAverage_id hab] at hh

theorem gap_binAverage_eq {p a b : ℝ} (hp : 0 ≤ p) (hpa : p ≤ a) (hab : a < b) (hb : b ≤ 1) :
    binAverage (fun z => activationPrimitive phi (z - p) - activationPrimitive phi z) a b =
      (primitiveMoment phi (b - p) - primitiveMoment phi (a - p) -
        (primitiveMoment phi b - primitiveMoment phi a)) / (b - a) := by
  have hc : ContinuousOn (activationPrimitive phi) (Icc a b) :=
    h.primitive_continuous.mono (Icc_subset_Icc (hp.trans hpa) hb)
  have hcs : ContinuousOn (fun z => activationPrimitive phi (z - p)) (Icc a b) := by
    apply h.primitive_continuous.comp (continuous_id.sub continuous_const).continuousOn
    intro z hz
    change 0 ≤ z - p ∧ z - p ≤ 1
    constructor <;> linarith [hz.1, hz.2]
  rw [binAverage_sub (hcs.intervalIntegrable_of_Icc hab.le) (hc.intervalIntegrable_of_Icc hab.le),
    h.primitive_binAverage (hp.trans hpa) hab hb]
  have hs : binAverage (fun z => activationPrimitive phi (z - p)) a b =
      (primitiveMoment phi (b - p) - primitiveMoment phi (a - p)) / (b - a) := by
    rw [binAverage, intervalIntegral.integral_comp_sub_right,
      ← h.moment_increment (by linarith) (by linarith) (by linarith)]
  rw [hs]
  ring

end NormalizedNecessaryTwoClass

namespace NormalizedNecessaryConditions
variable {L : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryConditions L phi)
include h

/-- Equation (D.1) for actual normalized necessary data and actual interval
averages. Only the numerical lower bounds on the two primitive ratios remain
premises, ready for the sequential dual certificates. -/
theorem moving_bin_row (hL0 : 0 < L) (hL1 : L < 1)
    {p a0 a1 b0 b1 z0 z1 x y : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (ha0 : 0 ≤ a0) (ha : a0 < a1) (haL : a1 < L) (hap : a1 < 1 - p)
    (hpb : p ≤ b0) (hb : b0 < b1) (hbL : b1 < L)
    (hz0 : L + p / 2 < z0) (hz : z0 < z1) (hz1 : z1 ≤ 1)
    (hk : 0 ≤ p + b0 - L) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxX : x ≤ activationPrimitive phi (1 - p) / activationPrimitive phi p)
    (hyY : y ≤ binAverage (fun z => activationPrimitive phi (z - p) - activationPrimitive phi z) z0 z1 /
      activationPrimitive phi p) :
    (((z0 + z1) / 2 - L) + (p + (b0 + b1) / 2 - L) * y) * binAverage phi a0 a1 +
    (((z0 + z1) / 2 - L) * x + (2 * L - (a0 + a1) / 2) * y) * binAverage phi b0 b1 +
    ((2 * L - (a0 + a1) / 2) - (p + (b0 + b1) / 2 - L) * x) * binAverage phi z0 z1 ≤ 0 := by
  let R := activationPrimitive phi p
  let P := activationPrimitive phi (1 - p)
  let K := binAverage (fun z => activationPrimitive phi (z - p) - activationPrimitive phi z) z0 z1
  have hR : 0 < R := h.primitive_pos p hp
  have hr := h.third_class_bin_average hL0 hL1 hp ha0 ha haL hap hpb hb hbL hz0 hz hz1 hk
  have hrow :
      (((z0 + z1) / 2 - L) + (p + (b0 + b1) / 2 - L) * (K / R)) * binAverage phi a0 a1 +
      (((z0 + z1) / 2 - L) * (P / R) + (2 * L - (a0 + a1) / 2) * (K / R)) * binAverage phi b0 b1 +
      ((2 * L - (a0 + a1) / 2) - (p + (b0 + b1) / 2 - L) * (P / R)) * binAverage phi z0 z1 ≤ 0 := by
    apply nonpos_of_mul_nonpos_left (b := R) ?_ hR
    calc
      _ = threeClassRow L p R P K ((a0 + a1) / 2) ((b0 + b1) / 2) ((z0 + z1) / 2)
          (binAverage phi a0 a1) (binAverage phi b0 b1) (binAverage phi z0 z1) := by
        unfold threeClassRow
        field_simp [ne_of_gt hR]
        <;> ring
      _ ≤ 0 := hr
  have hbinary : p * (P / R) ≤ L := by
    have hh := h.toNormalizedNecessaryTwoClass.two_class_all hL0 hL1 p 0 hp le_rfl hp.1.le hL0.le
    rw [← mul_div_assoc, div_le_iff₀ hR]
    simpa [R, P, activationPrimitive] using hh
  have ha1 : a1 ≤ 1 := haL.le.trans hL1.le
  have hb0 : 0 ≤ b0 := hp.1.le.trans hpb
  have hb1 : b1 ≤ 1 := hbL.le.trans hL1.le
  have hz0' : 0 ≤ z0 := by linarith [hp.1]
  have hA := h.toNormalizedNecessaryTwoClass.activation_binAverage_ceiling ha0 ha ha1
  have hB := h.toNormalizedNecessaryTwoClass.activation_binAverage_ceiling hb0 hb hb1
  have hC := h.toNormalizedNecessaryTwoClass.activation_binAverage_ceiling hz0' hz hz1
  apply three_class_ratio_lower_row hL0 hp.1 (by linarith) (by linarith)
    (by linarith) (by linarith [hp.1]) hx hy hxX hyY hbinary hA hB ?_ hrow
  linarith

end NormalizedNecessaryConditions
end OptimalG
