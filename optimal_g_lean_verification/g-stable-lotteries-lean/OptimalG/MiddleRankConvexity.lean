import OptimalG.PrimitiveBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen

/-! Convexity reduces the straight middle part of the high-rank test to its endpoints. -/
namespace OptimalG
open Set MeasureTheory

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem primitive_continuous : ContinuousOn (curvePrimitive phi) (Icc 0 1) := by
  have hh := intervalIntegral.continuousOn_primitive_interval'
    (h.integral_subinterval (a := 0) (b := 1) le_rfl (by norm_num) le_rfl)
    (show (0 : ℝ) ∈ Set.uIcc 0 1 by simp)
  change ContinuousOn (fun r => ∫ u in (0 : ℝ)..r, phi u) (Icc 0 1)
  simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hh

theorem primitive_hasDerivAt {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (curvePrimitive phi) (phi r) r := by
  exact intervalIntegral.integral_hasDerivAt_right
    (h.integral_subinterval le_rfl hr.1.le hr.2.le)
    ((h.continuous.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo r hr)
    (h.continuous.continuousAt (Icc_mem_nhds hr.1 hr.2))

/-- A linear score on [λ,z0], and slope at least -1 before z0, make Ψ3 convex there. -/
theorem thirdTest_middle_convex {p q beta eta z0 : ℝ}
    (hq : 0 ≤ q) (hqp : q ≤ p) (hpl : p ≤ lam) (hz0 : lam ≤ z0) (hz01 : z0 ≤ 1)
    (hb : 0 ≤ beta) (hline : ∀ z ∈ Icc lam z0, phi z = lam - z)
    (hfall : ∀ a b, 0 ≤ a → a ≤ b → b ≤ z0 → a - b ≤ phi b - phi a) :
    ConvexOn ℝ (Icc lam z0)
      (fun z => z + q - lam + beta * packingK phi p q z + eta * phi z) := by
  let G := fun z => z + q - lam + beta * packingK phi p q z + eta * (lam - z)
  have hcomp : ContinuousOn (fun z => curvePrimitive phi (z - p + q)) (Icc lam z0) := by
    apply h.primitive_continuous.comp ((continuous_id.sub continuous_const).add continuous_const).continuousOn
    intro z hz
    change 0 ≤ z - p + q ∧ z - p + q ≤ 1
    constructor <;> linarith [hz.1, hz.2]
  have hJ : ContinuousOn (curvePrimitive phi) (Icc lam z0) :=
    h.primitive_continuous.mono (Icc_subset_Icc h.lam_pos.le hz01)
  have hcont : ContinuousOn G (Icc lam z0) := by
    dsimp [G, packingK]
    fun_prop
  have hderiv (z : ℝ) (hz : z ∈ interior (Icc lam z0)) :
      HasDerivAt G (1 - eta + beta * (phi (z - p + q) + z - lam)) z := by
    rw [interior_Icc] at hz
    have hsarg : z - p + q ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hzarg : z ∈ Ioo (0 : ℝ) 1 := ⟨h.lam_pos.trans hz.1, hz.2.trans_le hz01⟩
    have hs := (h.primitive_hasDerivAt hsarg).comp z (((hasDerivAt_id z).sub_const p).add_const q)
    have hj := h.primitive_hasDerivAt hzarg
    have hd := ((((hasDerivAt_id z).add_const q).sub_const lam).add
      (((hs.sub hj).sub_const (curvePrimitive phi q)).const_mul beta)).add
      (((hasDerivAt_const z lam).sub (hasDerivAt_id z)).const_mul eta)
    have hlin := hline z ⟨hz.1.le, hz.2.le⟩
    convert hd using 1 <;> first | rfl | (simp only [id_eq, mul_one, zero_sub, hlin]; ring)
  have hconv : ConvexOn ℝ (Icc lam z0) G := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc lam z0) hcont
      (fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt)
    intro a ha b hb' hab
    rw [(hderiv a ha).deriv, (hderiv b hb').deriv]
    rw [interior_Icc] at ha hb'
    have hfalls := hfall (a - p + q) (b - p + q) (by linarith [ha.1])
      (by linarith) (by linarith [hb'.2])
    have hm := mul_nonneg hb (show 0 ≤ (phi (b - p + q) + b - lam) - (phi (a - p + q) + a - lam) by linarith)
    linarith
  apply hconv.congr
  intro z hz
  dsimp [G]
  rw [hline z hz]

/-- Only the two endpoints need checking on the straight middle segment. -/
theorem thirdTest_middle_of_endpoints {p q beta eta z0 : ℝ}
    (hq : 0 ≤ q) (hqp : q ≤ p) (hpl : p ≤ lam) (hz0 : lam ≤ z0) (hz01 : z0 ≤ 1)
    (hb : 0 ≤ beta) (hline : ∀ z ∈ Icc lam z0, phi z = lam - z)
    (hfall : ∀ a b, 0 ≤ a → a ≤ b → b ≤ z0 → a - b ≤ phi b - phi a)
    (hlow : lam + q - lam + beta * packingK phi p q lam + eta * phi lam ≤ 0)
    (hhigh : z0 + q - lam + beta * packingK phi p q z0 + eta * phi z0 ≤ 0) :
    ∀ z ∈ Icc lam z0, z + q - lam + beta * packingK phi p q z + eta * phi z ≤ 0 := by
  intro z hz
  have hh := (h.thirdTest_middle_convex (eta := eta) hq hqp hpl hz0 hz01 hb hline hfall).le_max_of_mem_Icc
    (left_mem_Icc.mpr hz0) (right_mem_Icc.mpr hz0) hz
  exact hh.trans (max_le hlow hhigh)

end VerifierCurve
end OptimalG
