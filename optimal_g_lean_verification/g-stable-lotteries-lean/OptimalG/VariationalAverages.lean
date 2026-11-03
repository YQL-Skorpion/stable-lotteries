import OptimalG.VariationalWeakStar
import OptimalG.VariationalContinuation

/-!
# Averaged controls

The essential-infimum field can be compared with averages of the original
controls. These lemmas work with absolutely continuous probability measures,
so they never evaluate an L-infinity class at an exceptional point.
-/

namespace OptimalG.Variational

open Set MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction

variable {I : Type*} [MeasurableSpace I] {mu nu : Measure I}

theorem EssentiallyBounded.integrable [IsFiniteMeasure mu] {f : I → ℝ}
    (hf : EssentiallyBounded f mu) (hmeas : AEStronglyMeasurable f mu) : Integrable f mu := by
  obtain ⟨B, hB⟩ := hf
  exact MemLp.integrable (by simp) (memLp_top_of_bound hmeas B
    (by simpa only [Real.norm_eq_abs] using hB))

theorem EssentiallyBounded.of_absolutelyContinuous {f : I → ℝ}
    (hf : EssentiallyBounded f mu) (hnu : nu ≪ mu) : EssentiallyBounded f nu := by
  obtain ⟨B, hB⟩ := hf
  exact ⟨B, hnu.ae_le hB⟩

/-- Every absolutely continuous probability average lies above the essential
infimum. -/
theorem essInf_le_probability_average [NeZero mu] [IsProbabilityMeasure nu]
    (f : I → ℝ) (hf : EssentiallyBounded f mu) (hmeas : AEStronglyMeasurable f mu)
    (hnu : nu ≪ mu) : essInf f mu ≤ ∫ i, f i ∂nu := by
  have hi := (hf.of_absolutelyContinuous hnu).integrable (hmeas.mono_ac hnu)
  have hlo := hnu.ae_le (ae_essInf_le hf.boundedBelow)
  have h := integral_mono_ae (integrable_const (essInf f mu)) hi hlo
  simpa using h

/-- Every strict epsilon-sublevel of an essentially bounded real function has
positive measure. This supplies the normalized controls used for approximation. -/
theorem essInf_sublevel_positive [NeZero mu] (f : I → ℝ)
    (hf : EssentiallyBounded f mu) {eps : ℝ} (heps : 0 < eps) :
    0 < mu {i | f i < essInf f mu + eps} := by
  by_contra hpos
  have hzero : mu {i | f i < essInf f mu + eps} = 0 := le_zero_iff.mp (le_of_not_gt hpos)
  have hae : ∀ᵐ i ∂mu, essInf f mu + eps ≤ f i := by
    rw [ae_iff]
    simpa only [not_le] using hzero
  have hl := le_essInf_of_ae_le (essInf f mu + eps) hae
    hf.boundedAbove.isCoboundedUnder_ge
  linarith

/-- Probability averages supported on strict sublevels approximate the
essential infimum arbitrarily well. -/
theorem exists_probability_average_near_essInf [NeZero mu] [IsFiniteMeasure mu]
    (f : I → ℝ) (hf : EssentiallyBounded f mu) (hmeas : AEStronglyMeasurable f mu)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ nu : Measure I, IsProbabilityMeasure nu ∧ nu ≪ mu ∧
      essInf f mu ≤ ∫ i, f i ∂nu ∧ ∫ i, f i ∂nu ≤ essInf f mu + eps := by
  let fm := hmeas.mk f
  have hmeq : f =ᵐ[mu] fm := hmeas.ae_eq_mk
  have hfm : EssentiallyBounded fm mu := by
    obtain ⟨B, hB⟩ := hf
    refine ⟨B, ?_⟩
    filter_upwards [hB, hmeq] with i hi hei
    rwa [← hei]
  let A : Set I := {i | fm i < essInf f mu + eps}
  have hA : MeasurableSet A := hmeas.measurable_mk measurableSet_Iio
  have hpos : 0 < mu A := by
    have heq := essInf_congr_ae hmeq
    simpa only [A, heq] using essInf_sublevel_positive fm hfm heps
  let nu : Measure I := ProbabilityTheory.cond mu A
  have hnu : nu ≪ mu := ProbabilityTheory.cond_absolutelyContinuous
  letI : IsProbabilityMeasure nu := ProbabilityTheory.cond_isProbabilityMeasure hpos.ne'
  refine ⟨nu, inferInstance, hnu, essInf_le_probability_average f hf hmeas hnu, ?_⟩
  have hi := (hf.of_absolutelyContinuous hnu).integrable (hmeas.mono_ac hnu)
  have hupper : ∀ᵐ i ∂nu, f i ≤ essInf f mu + eps := by
    have hmem : ∀ᵐ i ∂nu, i ∈ A := ProbabilityTheory.ae_cond_mem hA
    filter_upwards [hmem, hnu.ae_eq hmeq] with i hi hei
    rw [hei]
    exact hi.le
  have h := integral_mono_ae hi (integrable_const (essInf f mu + eps)) hupper
  simpa using h

/-- Measurable low-rank scores remain measurable after lifting to the two
control-rank coordinates. -/
theorem Admissible.control_scores_measurable {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) :
    AEStronglyMeasurable (fun c : Control => d.phi c.2.1) controlMeasure ∧
    AEStronglyMeasurable (fun c : Control => d.phi c.2.2) controlMeasure := by
  let hm := h.2.2.1.aestronglyMeasurable
  have hreps := ae_control_lowRanks (fun r => d.phi r = hm.mk d.phi r) hm.ae_eq_mk
  constructor
  · apply ((hm.measurable_mk.comp (measurable_fst.comp measurable_snd)).aestronglyMeasurable).congr
    filter_upwards [hreps] with c hc
    exact hc.1.symm
  · apply ((hm.measurable_mk.comp (measurable_snd.comp measurable_snd)).aestronglyMeasurable).congr
    filter_upwards [hreps] with c hc
    exact hc.2.symm

/-- The primitive coefficient has a measurable representative on the full
control space, including the initial cap segment. -/
theorem Admissible.control_primitive_measurable {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) :
    AEStronglyMeasurable (fun c : Control => primitive lam d c.1) controlMeasure := by
  let E := extendLowPrimitive (lowPrimitiveMap h)
  have hE : Continuous E := (extendLowPrimitive_lipschitz _ h.lowPrimitive_lipschitz.to_restrict).continuous
  let R : Control → ℝ := fun c => if c.1 ≤ ell then cap lam d.S c.1 else E c.1
  have hR : Measurable R := by
    apply Measurable.ite (measurableSet_le measurable_fst measurable_const)
    · dsimp [cap]
      fun_prop
    · exact hE.measurable.comp measurable_fst
  apply hR.aestronglyMeasurable.congr
  have hmem : ∀ᵐ c ∂controlMeasure, c ∈ controlDomain := ae_restrict_mem controlDomain_measurable
  filter_upwards [hmem] with c hc
  dsimp [R, primitive]
  split_ifs with he ht
  · rfl
  · have hp : c.1 ∈ Icc ell tEnd := ⟨le_of_lt (lt_of_not_ge he), ht⟩
    exact extendLowPrimitive_of_mem (lowPrimitiveMap h) ⟨c.1, hp⟩
  · have hp := hc.1.2
    norm_num [pHi, tEnd] at hp ht
    linarith

theorem Admissible.controlH_measurable {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (z u : ℝ) : AEStronglyMeasurable (controlH lam d z u) controlMeasure := by
  obtain ⟨hx, hy⟩ := h.control_scores_measurable
  have hR := h.control_primitive_measurable
  have hp : AEStronglyMeasurable (fun c : Control => c.1) controlMeasure :=
    measurable_fst.aestronglyMeasurable
  have hcx : AEStronglyMeasurable (fun c : Control => c.2.1) controlMeasure :=
    (measurable_fst.comp measurable_snd).aestronglyMeasurable
  have hcy : AEStronglyMeasurable (fun c : Control => c.2.2) controlMeasure :=
    (measurable_snd.comp measurable_snd).aestronglyMeasurable
  have hP : AEStronglyMeasurable (fun c : Control => quadratic lam (1 - c.1) - d.S)
      controlMeasure := by
    dsimp [quadratic]
    fun_prop
  have hQ : AEStronglyMeasurable (fun c : Control => quadratic lam (z - c.1) - d.S - u)
      controlMeasure := by
    dsimp [quadratic]
    fun_prop
  have hk := (hp.add hcy).sub (aestronglyMeasurable_const (b := lam))
  have hh := (aestronglyMeasurable_const (b := 2 * lam)).sub hcx
  have hM := (hk.mul hx).add (hh.mul hy)
  have hD := (hh.mul hR).sub (hk.mul hP)
  exact (((aestronglyMeasurable_const.mul ((hR.mul hx).add (hP.mul hy))).add
    (hQ.mul hM)).neg).div₀ hD

/-- A probability average of the actual controls is a supersolution field for
(4.3). -/
theorem Admissible.vectorField_le_average {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (nu : Measure Control) [IsProbabilityMeasure nu]
    (hnu : nu ≪ controlMeasure) (z u : ℝ) :
    vectorField lam d z u ≤ ∫ c, controlH lam d z u c ∂nu :=
  (min_le_right _ _).trans (essInf_le_probability_average _
    (h.controlH_bounded z u) (h.controlH_measurable z u) hnu)

end OptimalG.Variational
