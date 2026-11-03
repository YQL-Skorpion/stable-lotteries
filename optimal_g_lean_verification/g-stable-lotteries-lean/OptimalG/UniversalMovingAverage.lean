import OptimalG.UniversalAveragedRows

/-! Independent interval averaging of the three-class election inequality. -/
namespace OptimalG
open Set MeasureTheory

/-- The undivided three-class expression (3.7). -/
def threeClassRow (L p R P K x y z A B C : ℝ) : ℝ :=
  ((z - L) * R + (p + y - L) * K) * A +
  ((z - L) * P + (2 * L - x) * K) * B +
  ((2 * L - x) * R - (p + y - L) * P) * C

theorem threeClassRow_average_first {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (L p R P K y z B C : ℝ)
    (hrow : ∀ x ∈ Icc a b, threeClassRow L p R P K x y z (f x) B C ≤ 0) :
    threeClassRow L p R P K ((a + b) / 2) y z (binAverage f a b) B C ≤ 0 := by
  have hh := binAverage_affine_nonpos hab hf
    ((z - L) * R + (p + y - L) * K) (-K * B - R * C)
    (((z - L) * P + 2 * L * K) * B + (2 * L * R - (p + y - L) * P) * C)
    (fun x hx => by have hh := hrow x hx; unfold threeClassRow at hh; nlinarith only [hh])
  unfold threeClassRow
  nlinarith only [hh]

theorem threeClassRow_average_second {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (L p R P K x z A C : ℝ)
    (hrow : ∀ y ∈ Icc a b, threeClassRow L p R P K x y z A (f y) C ≤ 0) :
    threeClassRow L p R P K x ((a + b) / 2) z A (binAverage f a b) C ≤ 0 := by
  have hh := binAverage_affine_nonpos hab hf
    ((z - L) * P + (2 * L - x) * K) (K * A - P * C)
    (((z - L) * R + (p - L) * K) * A + ((2 * L - x) * R - (p - L) * P) * C)
    (fun y hy => by have hh := hrow y hy; unfold threeClassRow at hh; nlinarith only [hh])
  unfold threeClassRow
  nlinarith only [hh]

theorem threeClassRow_average_third {f K : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hK : IntervalIntegrable K volume a b)
    (L p R P x y A B : ℝ)
    (hrow : ∀ z ∈ Icc a b, threeClassRow L p R P (K z) x y z A B (f z) ≤ 0) :
    threeClassRow L p R P (binAverage K a b) x y ((a + b) / 2)
      A B (binAverage f a b) ≤ 0 := by
  have hh := binAverage_linear3_nonpos hab hf hK
    ((2 * L - x) * R - (p + y - L) * P) ((p + y - L) * A + (2 * L - x) * B)
    (R * A + P * B) (-L * (R * A + P * B))
    (fun z hz => by have hh := hrow z hz; unfold threeClassRow at hh; nlinarith only [hh])
  unfold threeClassRow
  nlinarith only [hh]

namespace NormalizedNecessaryConditions
variable {L : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryConditions L phi)
include h

/-- The bin domains used by the moving LP rows imply the strict sign condition
in (3.7), which is then supplied by the actual Election 3 construction. -/
theorem third_class_row (hL0 : 0 < L) (hL1 : L < 1)
    {p x y z : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hx : 0 ≤ x) (hxL : x < L) (hxp : x < 1 - p)
    (hpy : p ≤ y) (hyL : y < L) (hz : L + p / 2 < z) (hz1 : z ≤ 1)
    (hk : 0 ≤ p + y - L) :
    threeClassRow L p (activationPrimitive phi p) (activationPrimitive phi (1 - p))
      (activationPrimitive phi (z - p) - activationPrimitive phi z)
      x y z (phi x) (phi y) (phi z) ≤ 0 := by
  have hK := h.toNormalizedNecessaryTwoClass.third_class_K_pos hp.1 (hpy.trans_lt hyL) hz hz1
  have hR := h.primitive_pos p hp
  have hU : 0 < z - L := by linarith [hp.1]
  have hX : 0 < (z - L) * activationPrimitive phi p +
      (p + y - L) * (activationPrimitive phi (z - p) - activationPrimitive phi z) :=
    add_pos_of_pos_of_nonneg (mul_pos hU hR) (mul_nonneg hk hK.le)
  exact h.toNormalizedNecessaryTwoClass.third_class_of_weight_test hL0 hL1 hp hxL hpy hyL hz hz1 hX
    (h.third_class_test p x y z hp hx hxp hpy (hyL.trans hL1) (by linarith) hz1)

/-- Full independent averaging in x, then y, then z. All three averages are
actual interval integrals, and every pointwise row is proved from finite elections. -/
theorem third_class_bin_average (hL0 : 0 < L) (hL1 : L < 1)
    {p a0 a1 b0 b1 z0 z1 : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (ha0 : 0 ≤ a0) (ha : a0 < a1) (haL : a1 < L) (hap : a1 < 1 - p)
    (hpb : p ≤ b0) (hb : b0 < b1) (hbL : b1 < L)
    (hz0 : L + p / 2 < z0) (hz : z0 < z1) (hz1 : z1 ≤ 1)
    (hk : 0 ≤ p + b0 - L) :
    threeClassRow L p (activationPrimitive phi p) (activationPrimitive phi (1 - p))
      (binAverage (fun z => activationPrimitive phi (z - p) - activationPrimitive phi z) z0 z1)
      ((a0 + a1) / 2) ((b0 + b1) / 2) ((z0 + z1) / 2)
      (binAverage phi a0 a1) (binAverage phi b0 b1) (binAverage phi z0 z1) ≤ 0 := by
  have ha1 : a1 ≤ 1 := haL.le.trans hL1.le
  have hb0 : 0 ≤ b0 := hp.1.le.trans hpb
  have hb1 : b1 ≤ 1 := hbL.le.trans hL1.le
  have hz0' : 0 ≤ z0 := by linarith [hp.1]
  have hfa := (h.continuous.mono (Icc_subset_Icc ha0 ha1)).intervalIntegrable_of_Icc (μ := volume) ha.le
  have hfb := (h.continuous.mono (Icc_subset_Icc hb0 hb1)).intervalIntegrable_of_Icc (μ := volume) hb.le
  have hfz := (h.continuous.mono (Icc_subset_Icc hz0' hz1)).intervalIntegrable_of_Icc (μ := volume) hz.le
  have hcJ := h.toNormalizedNecessaryTwoClass.primitive_continuous
  have hKc : ContinuousOn (fun z => activationPrimitive phi (z - p) - activationPrimitive phi z) (Icc z0 z1) := by
    apply ContinuousOn.sub
    · apply hcJ.comp (continuous_id.sub continuous_const).continuousOn
      intro z hz'
      change 0 ≤ z - p ∧ z - p ≤ 1
      constructor <;> linarith [hz'.1, hz'.2, hp.1]
    · exact hcJ.mono (Icc_subset_Icc hz0' hz1)
  apply threeClassRow_average_third hz hfz (hKc.intervalIntegrable_of_Icc hz.le)
  intro z hz'
  apply threeClassRow_average_second hb hfb
  intro y hy
  apply threeClassRow_average_first ha hfa
  intro x hx
  exact h.third_class_row hL0 hL1 hp (ha0.trans hx.1) (hx.2.trans_lt haL) (hx.2.trans_lt hap)
    (hpb.trans hy.1) (hy.2.trans_lt hbL) (hz0.trans_le hz'.1) (hz'.2.trans hz1) (by linarith [hy.1])

end NormalizedNecessaryConditions
end OptimalG
