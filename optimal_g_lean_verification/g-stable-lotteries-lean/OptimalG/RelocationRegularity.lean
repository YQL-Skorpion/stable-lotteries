import OptimalG.RelocatedPrimitive
import OptimalG.SlackRemovalRegularity
import OptimalG.PrimitiveExtension

/-! Globally Lipschitz extensions of the concrete modified primitives. -/
namespace OptimalG.Relocation
open Set MeasureTheory
open scoped NNReal

noncomputable def firstExtendedPrimitive (lam : ℝ) (phi : ℝ → ℝ) (r : ℝ) : ℝ :=
  extendedPrimitive phi r + (slack lam phi r-firstSlack lam phi r)
noncomputable def secondExtendedPrimitive (lam : ℝ) (phi : ℝ → ℝ) (r : ℝ) : ℝ :=
  extendedPrimitive phi r + (slack lam phi r-secondSlack lam phi r)

theorem firstExtended_eq (lam : ℝ) (phi : ℝ → ℝ) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    firstExtendedPrimitive lam phi r = firstPrimitive lam phi r := by
  rw [firstExtendedPrimitive,extendedPrimitive_eq phi hr,slack_eq lam phi hr]
  unfold cumulativeSlack firstPrimitive
  ring

theorem secondExtended_eq (lam : ℝ) (phi : ℝ → ℝ) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    secondExtendedPrimitive lam phi r = secondPrimitive lam phi r := by
  rw [secondExtendedPrimitive,extendedPrimitive_eq phi hr,slack_eq lam phi hr]
  unfold cumulativeSlack secondPrimitive
  ring

variable {lam : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass lam phi)
include h

theorem slack_lipschitz : ∃ K : ℝ≥0, LipschitzWith K (slack lam phi) := by
  have hc : ContinuousOn (activationSlack lam phi) (Icc 0 1) :=
    (continuousOn_const.sub continuousOn_id).sub h.continuous
  obtain ⟨K,hK⟩ := extendedPrimitive_lipschitz hc
  have heq : slack lam phi = fun r => extendedPrimitive (activationSlack lam phi) (max 0 (min 1 r)) := by
    funext r
    have hr : max 0 (min 1 r) ∈ Icc (0 : ℝ) 1 :=
      ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
    rw [extendedPrimitive_eq _ hr]
    have hi := h.slack_integral (a := 0) le_rfl hr.1 hr.2
    have hzero : cumulativeSlack lam phi 0=0 := by
      simp [cumulativeSlack,linePrimitive,activationPrimitive]
    rw [hzero,sub_zero] at hi
    exact hi.symm
  rw [heq]
  refine ⟨K, ?_⟩
  simpa only [Function.comp_def,mul_one,id_eq] using
    hK.comp ((LipschitzWith.id.const_min 1).const_max 0)

theorem firstExtended_lipschitz : ∃ K : ℝ≥0, LipschitzWith K (firstExtendedPrimitive lam phi) := by
  obtain ⟨K,hK⟩ := extendedPrimitive_lipschitz h.continuous
  obtain ⟨KS,hKS⟩ := slack_lipschitz h
  have hD := drainSlack_lipschitz hKS (0.245 : ℝ) (fraction lam phi)
  have hF := flattenSlack_lipschitz hD (0.38 : ℝ) 0.44
  exact ⟨_, hK.add (hKS.sub hF)⟩

theorem secondExtended_lipschitz : ∃ K : ℝ≥0, LipschitzWith K (secondExtendedPrimitive lam phi) := by
  obtain ⟨K,hK⟩ := extendedPrimitive_lipschitz h.continuous
  obtain ⟨KS,hKS⟩ := slack_lipschitz h
  have hD := drainSlack_lipschitz hKS (0.245 : ℝ) (fraction lam phi)
  have hF := flattenSlack_lipschitz hD (0.38 : ℝ) 0.44
  have hG := flattenSlack_lipschitz hF (0.44 : ℝ) 0.775
  exact ⟨_, hK.add (hKS.sub hG)⟩

theorem firstSlack_nonneg (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) (r : ℝ) : 0 ≤ firstSlack lam phi r := by
  have ht := fraction_mem h hL hLP
  have hd (r : ℝ) : 0 ≤ drainSlack (slack lam phi) 0.245 (fraction lam phi) r := by
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (slack_nonneg h r))
      (mul_nonneg ht.1 (le_max_left _ _))
  exact add_nonneg (hd _) (le_max_left _ _)

theorem secondSlack_nonneg (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) (r : ℝ) : 0 ≤ secondSlack lam phi r :=
  add_nonneg (firstSlack_nonneg h hL hLP _) (le_max_left _ _)

theorem secondSlack_middle (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {r : ℝ} (hr : r ∈ Icc (0.38 : ℝ) 0.775) :
    secondSlack lam phi r = slack lam phi 0.38-prefixGain lam phi := by
  rw [secondSlack,firstSlack]
  rw [two_phase_middle (slack_monotone h) (fraction_mem h hL hLP)
    (by norm_num : (0.245 : ℝ) ≤ 0.38) (by norm_num : (0.38 : ℝ) ≤ 0.44)
    (by norm_num : (0.44 : ℝ) ≤ 0.775) hr,
    fraction_mul_prefix h hL hLP]

theorem secondPrimitive_middle (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {r : ℝ} (hr : r ∈ Icc (0.38 : ℝ) 0.775) :
    secondPrimitive lam phi r = linePrimitive lam r-(slack lam phi 0.38-prefixGain lam phi) := by
  rw [secondPrimitive,secondSlack_middle h hL hLP hr]

theorem firstExtended_ceiling (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    firstExtendedPrimitive lam phi r ≤ linePrimitive lam r := by
  rw [firstExtended_eq lam phi hr,firstPrimitive]
  linarith [firstSlack_nonneg h hL hLP r]

theorem secondExtended_ceiling (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    secondExtendedPrimitive lam phi r ≤ linePrimitive lam r := by
  rw [secondExtended_eq lam phi hr,secondPrimitive]
  linarith [secondSlack_nonneg h hL hLP r]

end OptimalG.Relocation
