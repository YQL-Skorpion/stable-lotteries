import OptimalG.SecondPhaseComparison
import OptimalG.PhaseContinuation

/-! A genuine signed continuation after the second explicit slack removal. -/
namespace OptimalG.Relocation
open Set Variational
open scoped NNReal

theorem exists_second_phase_continuation {lam : ℝ} {phi Y : ℝ → ℝ}
    (h : NormalizedNecessaryConditions lam phi) (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi)
    (hY0 : Y zStart=firstPrimitive lam phi zStart)
    (hYD : ∀ z ∈ Icc zStart zEnd,
      HasDerivWithinAt Y (rawVectorField lam (firstExtendedPrimitive lam phi) phi z (Y z)) (Icc zStart zEnd) z)
    (hYbounds : ∀ z ∈ Icc zStart zEnd,
      linePrimitive lam z-linePrimitive lam 1 ≤ Y z ∧ Y z ≤ linePrimitive lam z-firstSlack lam phi zStart) :
    ∃ Z : ℝ → ℝ, Z zStart=secondPrimitive lam phi zStart ∧
      (∀ z ∈ Icc zStart zEnd,
        HasDerivWithinAt Z (rawVectorField lam (secondExtendedPrimitive lam phi) phi z (Z z))
          (Icc zStart zEnd) z) ∧
      ∀ z ∈ Icc zStart zEnd,
        Y z+0.216*massTwo lam phi ≤ Z z ∧
        linePrimitive lam z-linePrimitive lam 1 ≤ Z z ∧ Z z ≤ linePrimitive lam z-secondSlack lam phi zStart := by
  obtain ⟨K,hK,ht⟩ := second_raw_regular h.toNormalizedNecessaryTwoClass hL hLP
  have hm := (mass_budget h.toNormalizedNecessaryTwoClass hL hLP).2.1
  have hstart : secondSlack lam phi zStart=firstSlack lam phi zStart-massTwo lam phi := by
    convert second_start_slack h.toNormalizedNecessaryTwoClass hL hLP using 1 <;> norm_num [zStart]
  obtain ⟨Z,hZ0,hZD,hZB⟩ := exists_phase_continuation hL
    (rawVectorField lam (firstExtendedPrimitive lam phi) phi)
    (rawVectorField lam (secondExtendedPrimitive lam phi) phi) K Y hm le_rfl
    (secondSlack_nonneg h.toNormalizedNecessaryTwoClass hL hLP zStart) hstart hK ht hY0 hYD hYbounds
    (fun z hz => second_raw_field_comparison h hL hLP hz (hYbounds z hz).1 (hYbounds z hz).2
      (phaseError_bounds hm hz))
    (fun _ _ => min_le_left _ _)
  refine ⟨Z,hZ0,hZD,?_⟩
  intro z hz
  have hb := hZB z hz
  exact ⟨by linarith [hb.1],hb.2⟩

end OptimalG.Relocation
