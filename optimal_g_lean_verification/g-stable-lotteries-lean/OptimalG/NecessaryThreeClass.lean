import OptimalG.ThreeClassTest
import OptimalG.NecessaryPrimitiveBounds

/-! # All three necessary election tests from actual finite equal-voter bounds -/

namespace OptimalG
open Set MeasureTheory

theorem normalized_three_class_weight_test (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1))
    (lam : ℝ) (hL0 : 0 < lam) (hL1 : lam < 1) (hbound : UniversalBound g (1 + 2 * lam))
    (phi : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hrelation : ∀ r ∈ Icc (0 : ℝ) 1, phi r = c * (activationPrimitive g 1 - g r))
    (hdata : NormalizedNecessaryTwoClass lam phi)
    (p x y z : ℝ) (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) (hxp : x < 1 - p)
    (hpy : p ≤ y) (hy1 : y < 1) (hpz : p < z) (hz1 : z ≤ 1) :
    ThreeClassWeightTest (activationPrimitive phi p) (activationPrimitive phi (1 - p))
      (activationPrimitive phi (z - p) - activationPrimitive phi z)
      (phi x) (phi y) (phi z) (2 * lam - x) (z - lam) (p + y - lam) := by
  let gc := clippedActivation g
  have hgc : Continuous gc := clippedActivation_continuous g hg
  have hbc : UniversalBound gc (1 + 2 * lam) := (universalBound_clipped_iff g _).mpr hbound
  have hphi (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      phi r = c * (activationPrimitive gc 1 - gc r) := by
    dsimp [gc]
    rw [activationPrimitive_clipped g (by norm_num), clippedActivation_eq g r hr]
    exact hrelation r hr
  have hJ (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      activationPrimitive phi r = c * centeredPrimitive gc r := by
    calc
      _ = activationPrimitive (fun t => c * (activationPrimitive gc 1 - gc t)) r := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hr.1] at ht
        exact hphi t ⟨ht.1, ht.2.trans hr.2⟩
      _ = _ := scaled_centered_primitive gc hgc c r
  have hR : 0 < centeredPrimitive gc p := by
    have hpos := hdata.primitive_pos hL0 hL1 p hp
    rw [hJ p ⟨hp.1.le, hp.2.le⟩] at hpos
    exact pos_of_mul_pos_right hpos hc.le
  have hP : 0 < centeredPrimitive gc (1 - p) := by
    have hp' : 1 - p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.2], by linarith [hp.1]⟩
    have hpos := hdata.primitive_pos hL0 hL1 (1 - p) hp'
    rw [hJ (1 - p) ⟨hp'.1.le, hp'.2.le⟩] at hpos
    exact pos_of_mul_pos_right hpos hc.le
  have ht := three_class_weight_test_of_universalBound gc hgc lam p x y z hL0.le hbc
    hp hx hxp hpy hy1 hpz hz1 hR hP
  have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx, by linarith [hp.1]⟩
  have hyI : y ∈ Icc (0 : ℝ) 1 := ⟨hp.1.le.trans hpy, hy1.le⟩
  have hzI : z ∈ Icc (0 : ℝ) 1 := ⟨hp.1.le.trans hpz.le, hz1⟩
  have hzpI : z - p ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hp.1]⟩
  have hK : activationPrimitive phi (z - p) - activationPrimitive phi z =
      c * (centeredPrimitive gc (z - p) - centeredPrimitive gc z) := by
    rw [hJ _ hzpI, hJ _ hzI]
    ring
  rw [hJ p ⟨hp.1.le, hp.2.le⟩, hJ (1 - p) ⟨by linarith [hp.2], by linarith [hp.1]⟩,
    hK, hphi x hxI, hphi y hyI, hphi z hzI]
  exact ht.scale c hc

/-- Necessary data for the lower-bound reduction. Every primitive is the
actual integral of phi; every weight test comes from actual finite elections. -/
structure NormalizedNecessaryConditions (lam : ℝ) (phi : ℝ → ℝ) : Prop
    extends NormalizedNecessaryTwoClass lam phi where
  primitive_pos : ∀ r ∈ Ioo (0 : ℝ) 1, 0 < activationPrimitive phi r
  third_class_test : ∀ p x y z : ℝ, p ∈ Ioo 0 1 → 0 ≤ x → x < 1 - p →
    p ≤ y → y < 1 → p < z → z ≤ 1 →
    ThreeClassWeightTest (activationPrimitive phi p) (activationPrimitive phi (1 - p))
      (activationPrimitive phi (z - p) - activationPrimitive phi z)
      (phi x) (phi y) (phi z) (2 * lam - x) (z - lam) (p + y - lam)

/-- Fully concrete Elections 1, 2 and 3 supply the normalized necessary
conditions for every continuous activation with a universal bound below 3. -/
theorem exists_normalized_necessary_conditions (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 1)) (lam : ℝ) (hL0 : 0 < lam) (hL1 : lam < 1)
    (hbound : UniversalBound g (1 + 2 * lam)) :
    ∃ (phi : ℝ → ℝ) (c : ℝ), 0 < c ∧
      (∀ r ∈ Icc (0 : ℝ) 1, phi r = c * (activationPrimitive g 1 - g r)) ∧
      NormalizedNecessaryConditions lam phi := by
  obtain ⟨phi, c, hc, hrelation, hdata⟩ := exists_normalized_necessary_twoClass g hg lam hL0.le hbound
  refine ⟨phi, c, hc, hrelation, ⟨hdata, hdata.primitive_pos hL0 hL1, ?_⟩⟩
  intro p x y z hp hx hxp hpy hy1 hpz hz1
  exact normalized_three_class_weight_test g hg lam hL0 hL1 hbound phi c hc hrelation hdata
    p x y z hp hx hxp hpy hy1 hpz hz1

end OptimalG
