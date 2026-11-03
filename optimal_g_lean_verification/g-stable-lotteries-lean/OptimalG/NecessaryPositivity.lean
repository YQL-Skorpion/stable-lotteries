import OptimalG.NecessaryPositivityCore
import OptimalG.NecessaryTwoClass

/-! Actual normalized necessary data have a positive integral primitive. -/
namespace OptimalG
open Set MeasureTheory

/-- Extending an activation by its endpoint values preserves every primitive
value on the actual rank interval. -/
theorem activationPrimitive_clipped (phi : ℝ → ℝ) {r : ℝ} (hr : r ∈ Icc 0 1) :
    activationPrimitive (clippedActivation phi) r = activationPrimitive phi r := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hr.1] at hx
  exact clippedActivation_eq phi x ⟨hx.1, hx.2.trans hr.2⟩

namespace NormalizedNecessaryTwoClass
variable {lam : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass lam phi)
include h

theorem primitive_tail_pos (hL0 : 0 ≤ lam) (hL1 : lam < 1)
    {r : ℝ} (hr : r ∈ Ico lam 1) : 0 < activationPrimitive phi r := by
  have hr0 : 0 ≤ r := hL0.trans hr.1
  have hInt0 := (h.continuous.mono (Icc_subset_Icc le_rfl hr.2.le)).intervalIntegrable_of_Icc (μ := volume) hr0
  have hInt1 := (h.continuous.mono (Icc_subset_Icc hr0 le_rfl)).intervalIntegrable_of_Icc (μ := volume) hr.2.le
  have hsum := intervalIntegral.integral_add_adjacent_intervals hInt0 hInt1
  have hline : IntervalIntegrable (fun x : ℝ => lam - x) volume r 1 :=
    (continuous_const.sub continuous_id).intervalIntegrable r 1
  have hbound := intervalIntegral.integral_mono_on hr.2.le hInt1 hline
    (fun x hx => h.ceiling x ⟨hr0.trans hx.1, hx.2⟩)
  rw [intervalIntegral.integral_sub intervalIntegrable_const (show IntervalIntegrable (fun x : ℝ => x) volume r 1 from continuous_id.intervalIntegrable r 1),
    intervalIntegral.integral_const, integral_id] at hbound
  change activationPrimitive phi r + (∫ x in r..1, phi x) = activationPrimitive phi 1 at hsum
  rw [h.integral_zero] at hsum
  have hprod : 0 < (1 - r) * ((1 + r) / 2 - lam) :=
    mul_pos (by linarith [hr.2]) (by linarith [hr.1])
  simp only [smul_eq_mul] at hbound
  nlinarith

/-- Strict positivity follows from genuine finite-election necessary tests,
with no added shape or concavity assumption on the score. -/
theorem primitive_pos (hL0 : 0 < lam) (hL1 : lam < 1) :
    ∀ r ∈ Ioo (0 : ℝ) 1, 0 < activationPrimitive phi r := by
  let psi := clippedActivation phi
  have hpsi : Continuous psi := clippedActivation_continuous phi h.continuous
  have hd (r : ℝ) : HasDerivAt (activationPrimitive psi) (psi r) r :=
    intervalIntegral.integral_hasDerivAt_right (hpsi.intervalIntegrable 0 r)
      (hpsi.stronglyMeasurableAtFilter volume _) hpsi.continuousAt
  have hJ : Continuous (activationPrimitive psi) :=
    continuous_iff_continuousAt.mpr (fun r => (hd r).continuousAt)
  have heq (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      activationPrimitive psi r = activationPrimitive phi r := activationPrimitive_clipped phi hr
  have hJ1 : activationPrimitive psi 1 = 0 := (heq 1 (by norm_num)).trans h.integral_zero
  have hep : psi 1 ≤ -1 := by simpa only [psi, clippedActivation_eq phi 1 (by norm_num)] using h.endpoint
  have hp := primitive_positive_of_two_class hJ hd
    (by simp [activationPrimitive]) hJ1 hep hL0 hL1
    (fun r hr => by rw [heq r ⟨hL0.le.trans hr.1, hr.2.le⟩]; exact h.primitive_tail_pos hL0.le hL1 hr)
    (fun p q hp hq hqp hqlam hR => by
      have hpr : p ∈ Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
      have hqr : q ∈ Icc (0 : ℝ) 1 := ⟨hq, hqp.trans hp.2.le⟩
      have hrank : 1 - p + q ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hp.2], by linarith⟩
      rw [heq p hpr] at hR
      rw [heq p hpr, heq q hqr, heq _ hrank]
      exact h.two_class p q hp hq hqp hqlam hR)
  intro r hr
  rw [← heq r ⟨hr.1.le, hr.2.le⟩]
  exact hp r hr

/-- After positivity is proved, all interior two-class tests are unconditional. -/
theorem two_class_all (hL0 : 0 < lam) (hL1 : lam < 1)
    (p q : ℝ) (hp : p ∈ Ioo 0 1) (hq : 0 ≤ q) (hqp : q ≤ p) (hqlam : q ≤ lam) :
    p * (activationPrimitive phi (1 - p + q) - activationPrimitive phi q) ≤
      (lam - q) * activationPrimitive phi p :=
  h.two_class p q hp hq hqp hqlam (h.primitive_pos hL0 hL1 p hp)

end NormalizedNecessaryTwoClass
end OptimalG
