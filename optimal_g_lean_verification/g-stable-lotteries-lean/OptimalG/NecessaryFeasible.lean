import OptimalG.FirstPhaseContinuation
import OptimalG.SecondPhaseContinuation
import OptimalG.RelocationTerminal
import OptimalG.RelocationFeasible

/-! The complete analytic B.1 reduction, including both actual signed ODE
continuations, the repaired running envelope, and all terminal tests. -/
namespace OptimalG
open Set Variational Relocation

namespace NormalizedNecessaryConditions
variable {lam : ℝ} {phi : ℝ → ℝ} (h : OptimalG.NormalizedNecessaryConditions lam phi)
include h

/-- Necessary finite-election inequalities and the three explicit LP bounds
imply genuine variational feasibility, with no trajectory or envelope premise. -/
theorem variational_feasible (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) : Feasible lam := by
  obtain ⟨Y,hY0,hYD,hYB⟩ := h.exists_initial_signed_continuation hL hLP
  have hYbounds (z : ℝ) (hz : z ∈ Icc zStart zEnd) :
      linePrimitive lam z-linePrimitive lam 1 ≤ Y z ∧ Y z ≤ linePrimitive lam z-slack lam phi zStart := by
    have hzI : z ∈ Icc (0 : ℝ) 1 := by
      norm_num [zStart,zEnd] at hz
      exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
    have hlo := h.toNormalizedNecessaryTwoClass.primitive_reverse_lower hzI
    have hb := hYB z hz
    constructor
    · unfold linePrimitive
      norm_num
      linarith [hb.1]
    · rw [slack_eq lam phi (by norm_num [zStart])]
      exact hb.2
  obtain ⟨Y1,hY10,hY1D,hY1B⟩ := exists_first_phase_continuation h hL hLP hY0 hYD hYbounds
  obtain ⟨Y2,hY20,hY2D,hY2B⟩ := exists_second_phase_continuation h hL hLP hY10 hY1D
    (fun z hz => (hY1B z hz).2)
  have hflow (z : ℝ) (hz : z ∈ Icc zStart zEnd) :
      Y z+prefixGain lam phi+0.216*(massOne lam phi+massTwo lam phi) ≤ Y2 z := by
    have h1 := (hY1B z hz).1
    have h2 := (hY2B z hz).1
    linarith
  have hterm := second_terminal_tests h.toNormalizedNecessaryTwoClass hL hLP hflow
    (h.initial_binary_terminal_tests hL (fun z hz => (hYB z hz).1))
  apply feasible_of_second_continuation h.toNormalizedNecessaryTwoClass hL hLP hY2D
    (fun z hz => by simpa only [quadratic,linePrimitive] using (hY2B z hz).2.1) ?_ ?_
  · intro z hz
    have hb := (hY2B z hz).2.2
    rw [secondSlack_middle h.toNormalizedNecessaryTwoClass hL hLP (by norm_num [zStart])] at hb
    simpa only [quadratic,linePrimitive,finalScalar] using hb
  · intro z hz q hq
    obtain ⟨hm1,hm2,_⟩ := mass_budget h.toNormalizedNecessaryTwoClass hL hLP
    have ht := hterm z hz q hq
    linarith

end NormalizedNecessaryConditions
end OptimalG
