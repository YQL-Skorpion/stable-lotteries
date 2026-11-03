import OptimalG.PhaseControlComparison
import OptimalG.VariationalEnvelope
import OptimalG.VariationalDefs
import OptimalG.Certificates.Transcendental

/-! Quantitative propagation of the two slack-removal phases. -/
namespace OptimalG
open Set MeasureTheory Real
open scoped NNReal

/-- A clipped comparison passes to essential infima even when the active
control changes and no minimizing index exists. -/
theorem clipped_essInf_comparison {I : Type*} [MeasurableSpace I]
    {mu : Measure I} [NeZero mu] {f g : I → ℝ} {C err : ℝ}
    (herr : 0 ≤ err) (hf : Variational.EssentiallyBounded f mu)
    (hg : Variational.EssentiallyBounded g mu)
    (hfg : ∀ᵐ i ∂mu, min C (f i) - err ≤ min C (g i)) :
    min C (essInf f mu) - err ≤ min C (essInf g mu) := by
  apply le_min
  · have hh := min_le_left C (essInf f mu)
    linarith
  · apply le_essInf_of_ae_le _ _ hg.boundedAbove.isCoboundedUnder_ge
    filter_upwards [ae_essInf_le hf.boundedBelow, hfg] with i hi hfi
    have hh := min_le_min_left C hi
    have hg' := min_le_right C (g i)
    linarith

namespace Variational

noncomputable def phaseError (mu z : ℝ) : ℝ :=
  gronwallBound 0 4.53 (6.19 * mu) (z - zStart)

theorem phaseError_start (mu : ℝ) : phaseError mu zStart = 0 := by
  simp [phaseError, gronwallBound_x0]

theorem phaseError_hasDerivAt (mu z : ℝ) :
    HasDerivAt (phaseError mu) (4.53 * phaseError mu z + 6.19 * mu) z := by
  exact hasDerivAt_gronwallBound_shift 0 4.53 (6.19 * mu) z zStart

theorem phaseError_continuous (mu : ℝ) : Continuous (phaseError mu) :=
  continuous_iff_continuousAt.mpr (fun z => (phaseError_hasDerivAt mu z).continuousAt)

theorem phaseError_bounds {mu z : ℝ} (hmu : 0 ≤ mu) (hz : z ∈ Icc zStart zEnd) :
    0 ≤ phaseError mu z ∧ phaseError mu z ≤ 0.784 * mu := by
  have hz0 : 0 ≤ z - zStart := sub_nonneg.mpr hz.1
  have hz1 : 4.53 * (z - zStart) ≤ (0.453 : ℝ) := by
    norm_num [zStart, zEnd] at hz ⊢
    linarith [hz.2]
  have hexp0 : 1 ≤ exp (4.53 * (z - zStart)) := Real.one_le_exp (by positivity)
  have hexp1 := Real.exp_le_exp.mpr hz1
  have hloss := Certificates.propagation_loss_lt
  have hbound : (6.19 : ℝ) / 4.53 * (exp (4.53 * (z - zStart)) - 1) ≤ 0.784 := by
    nlinarith
  have heq : phaseError mu z =
      ((6.19 : ℝ) / 4.53 * (exp (4.53 * (z - zStart)) - 1)) * mu := by
    unfold phaseError gronwallBound
    norm_num
    ring
  rw [heq]
  exact ⟨mul_nonneg (by positivity) hmu, mul_le_mul_of_nonneg_right hbound hmu⟩

/-- Comparison with the actual error subsolution, retaining the initial mass
increase and the explicit 0.216 surviving fraction throughout the interval. -/
theorem phase_propagation
    (F G : ℝ → ℝ → ℝ) (L : ℝ≥0) (Y Z : ℝ → ℝ) (eta mu : ℝ)
    (hmu : 0 ≤ mu)
    (hG : ∀ z ∈ Ico zStart zEnd, LipschitzWith L (G z))
    (hY : ContinuousOn Y (Icc zStart zEnd)) (hZ : ContinuousOn Z (Icc zStart zEnd))
    (hYd : ∀ z ∈ Ico zStart zEnd, HasDerivWithinAt Y (F z (Y z)) (Ici z) z)
    (hZd : ∀ z ∈ Ico zStart zEnd, HasDerivWithinAt Z (G z (Z z)) (Ici z) z)
    (hfield : ∀ z ∈ Ico zStart zEnd,
      F z (Y z) - (6.19 * mu + 4.53 * phaseError mu z) ≤
        G z (Y z + eta + mu - phaseError mu z))
    (hinit : Y zStart + eta + mu ≤ Z zStart) :
    ∀ z ∈ Icc zStart zEnd, Y z + eta + 0.216 * mu ≤ Z z := by
  let W : ℝ → ℝ := fun z => Y z + eta + mu - phaseError mu z
  have hW : ContinuousOn W (Icc zStart zEnd) :=
    ((hY.add continuousOn_const).add continuousOn_const).sub (phaseError_continuous mu).continuousOn
  have hWd (z : ℝ) (hz : z ∈ Ico zStart zEnd) :
      HasDerivWithinAt W (F z (Y z) - (4.53 * phaseError mu z + 6.19 * mu)) (Ici z) z :=
    ((hYd z hz).add_const eta |>.add_const mu).sub (phaseError_hasDerivAt mu z).hasDerivWithinAt
  have hh := scalar_ode_comparison G L W Z
    (fun z => F z (Y z) - (4.53 * phaseError mu z + 6.19 * mu))
    (fun z => G z (Z z)) zStart zEnd hG hW hZ hWd hZd
    (fun z hz => by simpa only [W, add_comm (4.53 * phaseError mu z)] using hfield z hz)
    (fun _ _ => le_rfl) (by simpa [W, phaseError_start] using hinit)
  intro z hz
  have hb := (phaseError_bounds hmu hz).2
  have hw := hh z hz
  dsimp [W] at hw
  linarith

/-- The two phases improve the terminal margin by a strictly positive amount
unless no middle-rank slack was removed. -/
theorem two_phase_terminal_margin {Y Z T T' mu1 mu2 : ℝ}
    (h1 : 0 ≤ mu1) (h2 : 0 ≤ mu2)
    (hflow : Y + 2.98 * mu1 + 0.216 * (mu1 + mu2) ≤ Z)
    (hbarrier : T' ≤ T + 3.100 * mu1) :
    Y - T + 0.096 * mu1 + 0.216 * mu2 ≤ Z - T' := by
  linarith

end Variational
end OptimalG
