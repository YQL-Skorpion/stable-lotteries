import OptimalG.FirstPhaseField
import OptimalG.PhaseContinuation

/-! A genuine signed continuation after the first explicit slack removal. -/
namespace OptimalG.Relocation
open Set Variational
open scoped NNReal

theorem exists_first_phase_continuation {lam : ℝ} {phi Y : ℝ → ℝ}
    (h : NormalizedNecessaryConditions lam phi) (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi)
    (hY0 : Y zStart=activationPrimitive phi zStart)
    (hYD : ∀ z ∈ Icc zStart zEnd,
      HasDerivWithinAt Y (rawVectorField lam (extendedPrimitive phi) phi z (Y z)) (Icc zStart zEnd) z)
    (hYbounds : ∀ z ∈ Icc zStart zEnd,
      linePrimitive lam z-linePrimitive lam 1 ≤ Y z ∧ Y z ≤ linePrimitive lam z-slack lam phi zStart) :
    ∃ Z : ℝ → ℝ, Z zStart=firstPrimitive lam phi zStart ∧
      (∀ z ∈ Icc zStart zEnd,
        HasDerivWithinAt Z (rawVectorField lam (firstExtendedPrimitive lam phi) phi z (Z z))
          (Icc zStart zEnd) z) ∧
      ∀ z ∈ Icc zStart zEnd,
        Y z+prefixGain lam phi+0.216*massOne lam phi ≤ Z z ∧
        linePrimitive lam z-linePrimitive lam 1 ≤ Z z ∧ Z z ≤ linePrimitive lam z-firstSlack lam phi zStart := by
  obtain ⟨K,hK,ht⟩ := first_raw_regular h hL hLP
  have hm := (mass_budget h.toNormalizedNecessaryTwoClass hL hLP).1
  have heta : 0 ≤ prefixGain lam phi := mul_nonneg (by norm_num) hm
  have hstart : firstSlack lam phi zStart=slack lam phi zStart-(prefixGain lam phi+massOne lam phi) := by
    rw [first_after_eq h.toNormalizedNecessaryTwoClass hL hLP (by norm_num [zStart])]
    ring
  have hY0' : Y zStart=linePrimitive lam zStart-slack lam phi zStart := by
    rw [hY0,slack_eq lam phi (by norm_num [zStart])]
    unfold cumulativeSlack
    ring
  obtain ⟨Z,hZ0,hZD,hZB⟩ := exists_phase_continuation hL
    (rawVectorField lam (extendedPrimitive phi) phi)
    (rawVectorField lam (firstExtendedPrimitive lam phi) phi) K Y hm
    (show massOne lam phi ≤ prefixGain lam phi+massOne lam phi by linarith)
    (firstSlack_nonneg h.toNormalizedNecessaryTwoClass hL hLP zStart) hstart hK ht hY0' hYD hYbounds
    (fun z hz => by
      have hf := first_raw_field_comparison h hL hLP hz (hYbounds z hz).1 (hYbounds z hz).2
        (phaseError_bounds hm hz)
      simpa only [add_assoc] using hf)
    (fun _ _ => min_le_left _ _)
  refine ⟨Z,hZ0,hZD,?_⟩
  intro z hz
  have hb := hZB z hz
  exact ⟨by linarith [hb.1],hb.2⟩

end OptimalG.Relocation
