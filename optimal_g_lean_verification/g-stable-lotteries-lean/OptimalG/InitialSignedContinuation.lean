import OptimalG.PrimitiveExtension
import OptimalG.NecessaryThreeClass
import OptimalG.UniversalControlBoxes
import OptimalG.SignedRationalControl

/-! The initial signed continuation is an actual ODE solution derived from the
finite-election necessary conditions. Its lower trajectory is the original
integral primitive; its upper trajectory has constant cumulative slack. -/
namespace OptimalG
open Variational Set MeasureTheory
open scoped NNReal

private theorem control_boxes {c : Control} (hc : c ∈ controlDomain) :
    c.1 ∈ Icc (0.25 : ℝ) 0.36 ∧ c.2.1 ∈ Icc (0.285 : ℝ) 0.38 ∧
      c.2.2 ∈ Icc (0.285 : ℝ) 0.38 ∧ c.1 ≤ c.2.2 := by
  have hyl := (le_max_left xLo c.1).trans hc.2.2.1
  have hpy := (le_max_right xLo c.1).trans hc.2.2.1
  refine ⟨?_, ?_, ?_, hpy⟩
  · convert! hc.1 using 1; norm_num [pLo,pHi]
  · convert! hc.2.1 using 1; norm_num [xLo,xHi]
  · convert! (show c.2.2 ∈ Icc xLo xHi from ⟨hyl,hc.2.2.2⟩) using 1; norm_num [xLo,xHi]

private theorem time_box {z : ℝ} (hz : z ∈ Icc zStart zEnd) :
    z ∈ Icc (0.775 : ℝ) 0.875 := by
  convert! hz using 1; norm_num [zStart,zEnd]

namespace NormalizedNecessaryConditions
variable {lam : ℝ} {phi : ℝ → ℝ} (h : OptimalG.NormalizedNecessaryConditions lam phi)
include h

theorem initial_raw_determinant (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) (c : Control) (hc : c ∈ controlDomain) :
    (0.0535 : ℝ) ≤ rawDet lam (extendedPrimitive phi) c := by
  obtain ⟨hp,hx,hy,_⟩ := control_boxes hc
  unfold rawDet
  rw [extendedPrimitive_eq phi ⟨by linarith [hp.1],by linarith [hp.2]⟩,
    extendedPrimitive_eq phi ⟨by linarith [hp.2],by linarith [hp.1]⟩]
  exact h.toNormalizedNecessaryTwoClass.initial_determinant_margin hL hLP hp hx hy

theorem initial_raw_scores_bounded :
    EssentiallyBounded (fun c : Control => phi c.2.1) controlMeasure ∧
      EssentiallyBounded (fun c : Control => phi c.2.2) controlMeasure := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn h.continuous
  have hm : ∀ᵐ c ∂controlMeasure, c ∈ controlDomain := ae_restrict_mem controlDomain_measurable
  refine ⟨⟨C, ?_⟩,⟨C, ?_⟩⟩
  · filter_upwards [hm] with c hc
    obtain ⟨_,hx,_,_⟩ := control_boxes hc
    exact hC c.2.1 ⟨by linarith [hx.1],by linarith [hx.2]⟩
  · filter_upwards [hm] with c hc
    obtain ⟨_,_,hy,_⟩ := control_boxes hc
    exact hC c.2.2 ⟨by linarith [hy.1],by linarith [hy.2]⟩

/-- Each individual rational control dominates the original score, including
when the original low-rank scores have either sign. -/
theorem initial_raw_control_bound (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {z : ℝ} (hz : z ∈ Icc zStart zEnd)
    (c : Control) (hc : c ∈ controlDomain) :
    phi z ≤ signedControlH lam (extendedPrimitive phi)
      (rawAlpha lam (extendedPrimitive phi) phi)
      (rawBeta lam (extendedPrimitive phi) phi) (·.1) z (extendedPrimitive phi z) c := by
  obtain ⟨hp,hx,hy,hpy⟩ := control_boxes hc
  have hzt := time_box hz
  have hL0 : 0 < lam := by linarith [hL.1]
  have hL1 : lam < 1 := by linarith [hL.2]
  have hpI : c.1 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1],by linarith [hp.2]⟩
  have hxL : c.2.1 < lam := by linarith [hx.2,hL.1]
  have hyL : c.2.2 < lam := by linarith [hy.2,hL.1]
  have hzc : lam + c.1 / 2 < z := by linarith [hzt.1,hp.2,hL.2]
  have hz1 : z ≤ 1 := by linarith [hzt.2]
  have hX := (h.toNormalizedNecessaryTwoClass.initial_control_coefficients_positive hL hLP hp hx hy hzt).1
  have htest := h.third_class_test c.1 c.2.1 c.2.2 z hpI
    (by linarith [hx.1]) (by linarith [hx.2,hp.2]) hpy
    (by linarith [hy.2]) (by linarith [hp.2,hzt.1]) hz1
  have hh := h.toNormalizedNecessaryTwoClass.third_class_of_weight_test hL0 hL1
    hpI hxL hpy hyL hzc hz1 hX htest
  rw [rawControl_eq_value]
  rw [extendedPrimitive_eq phi ⟨hpI.1.le,hpI.2.le⟩,
    extendedPrimitive_eq phi ⟨by linarith [hp.2],by linarith [hp.1]⟩,
    extendedPrimitive_eq phi ⟨by linarith [hzt.1,hp.2],by linarith [hzt.2,hp.1]⟩,
    extendedPrimitive_eq phi ⟨by linarith [hzt.1],hz1⟩]
  have hD := h.toNormalizedNecessaryTwoClass.third_class_determinant_pos hL0 hL1 hpI hxL hyL
  unfold Certificates.Control.value Certificates.Control.alphaNumerator Certificates.Control.det
  apply (le_div_iff₀ hD).mpr
  nlinarith only [hh]

/-- The original primitive is a subsolution of the essential-infimum field. -/
theorem initial_raw_subsolution (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {z : ℝ} (hz : z ∈ Icc zStart zEnd) :
    phi z ≤ rawVectorField lam (extendedPrimitive phi) phi z (extendedPrimitive phi z) := by
  obtain ⟨K,hK⟩ := extendedPrimitive_lipschitz h.continuous
  have hs := h.initial_raw_scores_bounded
  have hab := raw_coefficients_bounded hK (by norm_num : (0 : ℝ) < 0.0535)
    (h.initial_raw_determinant hL hLP) hs.1 hs.2
  have hb := signedControlH_bounded (lam := lam) hK hab.1 hab.2 control_coordinates_bounded.1
    z (extendedPrimitive phi z)
  apply le_min
  · have hz' := time_box hz
    exact h.ceiling z ⟨by linarith [hz'.1],by linarith [hz'.2]⟩
  · apply le_essInf_of_ae_le _ _ hb.boundedAbove.isCoboundedUnder_ge
    have hm : ∀ᵐ c ∂controlMeasure, c ∈ controlDomain := ae_restrict_mem controlDomain_measurable
    exact hm.mono fun c hc => h.initial_raw_control_bound hL hLP hz c hc

/-- The signed field has a finite state Lipschitz constant and is continuous
in time for the actual primitive and score. -/
theorem initial_raw_regular (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) :
    ∃ K : ℝ≥0, (∀ z, LipschitzWith K (rawVectorField lam (extendedPrimitive phi) phi z)) ∧
      ∀ u, Continuous (fun z => rawVectorField lam (extendedPrimitive phi) phi z u) := by
  obtain ⟨K,hK⟩ := extendedPrimitive_lipschitz h.continuous
  have hs := h.initial_raw_scores_bounded
  exact rawVectorField_regular hK (by norm_num : (0 : ℝ) < 0.0535)
    (h.initial_raw_determinant hL hLP) hs.1 hs.2

/-- The original primitive and its constant-slack upper trajectory both lie
inside the fixed bounded state truncation. -/
theorem initial_raw_barriers (hL : Certificates.Compact.LambdaRange lam)
    {z : ℝ} (hz : z ∈ Icc zStart zEnd) :
    (extendedPrimitive phi z ∈ Icc (-1 : ℝ) 1) ∧
    (linePrimitive lam z - cumulativeSlack lam phi zStart ∈ Icc (-1 : ℝ) 1) ∧
    extendedPrimitive phi z ≤ linePrimitive lam z - cumulativeSlack lam phi zStart := by
  have hzt := time_box hz
  have hzI : z ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hzt.1],by linarith [hzt.2]⟩
  rw [extendedPrimitive_eq phi ⟨hzI.1.le,hzI.2.le⟩]
  have hJpos := h.primitive_pos z hzI
  have hS0 := h.toNormalizedNecessaryTwoClass.cumulativeSlack_nonneg
    (r := zStart) (by norm_num [zStart])
  have hSm := h.toNormalizedNecessaryTwoClass.cumulativeSlack_mono
    (a := zStart) (by norm_num [zStart]) hz.1 hzI.2.le
  have hcompare : activationPrimitive phi z ≤ linePrimitive lam z - cumulativeSlack lam phi zStart := by
    unfold cumulativeSlack at hSm ⊢
    linarith
  have hQ : linePrimitive lam z < 1 := by
    have hm := mul_le_mul hL.2 hzI.2.le hzI.1.le (by norm_num : (0 : ℝ) ≤ 0.562330)
    unfold linePrimitive
    nlinarith [sq_nonneg z]
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,hcompare⟩

/-- The actual signed ODE trajectory starts at the original primitive and is
trapped between that primitive and the constant-slack quadratic trajectory. -/
theorem exists_initial_signed_continuation (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) :
    ∃ Y : ℝ → ℝ, Y zStart = activationPrimitive phi zStart ∧
      (∀ z ∈ Icc zStart zEnd,
        HasDerivWithinAt Y (rawVectorField lam (extendedPrimitive phi) phi z (Y z))
          (Icc zStart zEnd) z) ∧
      ∀ z ∈ Icc zStart zEnd, activationPrimitive phi z ≤ Y z ∧
        Y z ≤ linePrimitive lam z - cumulativeSlack lam phi zStart := by
  obtain ⟨K,hK,ht⟩ := h.initial_raw_regular hL hLP
  obtain ⟨KJ,hJ⟩ := extendedPrimitive_lipschitz h.continuous
  let high := fun z => linePrimitive lam z - cumulativeSlack lam phi zStart
  have hhigh : Continuous high := by
    unfold high linePrimitive
    fun_prop
  have hhighD (z : ℝ) : HasDerivAt high (lam-z) z := by
    have hd := (((hasDerivAt_id z).const_mul lam).sub
      (((hasDerivAt_id z).pow 2).div_const 2)).sub_const (cumulativeSlack lam phi zStart)
    convert! hd using 1 <;> simp
  have hsub : ∀ z ∈ Ico zStart zEnd, clippedActivation phi z ≤
      rawVectorField lam (extendedPrimitive phi) phi z (extendedPrimitive phi z) := by
    intro z hz
    have hzt := time_box ⟨hz.1,hz.2.le⟩
    rw [clippedActivation_eq phi z ⟨by linarith [hzt.1],by linarith [hzt.2]⟩]
    exact h.initial_raw_subsolution hL hLP ⟨hz.1,hz.2.le⟩
  have hsuper : ∀ z ∈ Ico zStart zEnd,
      rawVectorField lam (extendedPrimitive phi) phi z (high z) ≤ lam-z :=
    fun _ _ => min_le_left _ _
  have hlowB : ∀ z ∈ Icc zStart zEnd, extendedPrimitive phi z ∈ Icc (-1 : ℝ) 1 :=
    fun z hz => (h.initial_raw_barriers hL hz).1
  have hhighB : ∀ z ∈ Icc zStart zEnd, high z ∈ Icc (-1 : ℝ) 1 :=
    fun z hz => (h.initial_raw_barriers hL hz).2.1
  have hinit : extendedPrimitive phi zStart ≤ activationPrimitive phi zStart ∧
      activationPrimitive phi zStart ≤ high zStart := by
    rw [extendedPrimitive_eq phi (by norm_num [zStart])]
    refine ⟨le_rfl,?_⟩
    unfold high cumulativeSlack
    linarith
  obtain ⟨Y,hY0,hYD,hYbounds⟩ := exists_continuation_between
    (rawVectorField lam (extendedPrimitive phi) phi) K
    (extendedPrimitive phi) high (clippedActivation phi) (fun z => lam-z)
    zStart zEnd (activationPrimitive phi zStart) (by norm_num [zStart,zEnd])
    (fun z _ => hK z) (fun u => (ht u).continuousOn) hJ.continuous.continuousOn
    hhigh.continuousOn
    (fun z _ => (extendedPrimitive_hasDerivAt h.continuous z).hasDerivWithinAt)
    (fun z _ => (hhighD z).hasDerivWithinAt) hsub hsuper hlowB hhighB hinit
  refine ⟨Y,hY0,hYD,?_⟩
  intro z hz
  have hb := hYbounds z hz
  have hzt := time_box hz
  rw [extendedPrimitive_eq phi ⟨by linarith [hzt.1],by linarith [hzt.2]⟩] at hb
  exact hb

/-- Every trajectory above the original primitive inherits its actual binary
terminal tests, before the later slack-relocation and envelope operations. -/
theorem initial_binary_terminal_tests (hL : Certificates.Compact.LambdaRange lam)
    {Y : ℝ → ℝ}
    (hY : ∀ z ∈ Icc zStart zEnd, activationPrimitive phi z ≤ Y z) :
    ∀ z ∈ Icc zTest zEnd, ∀ q ∈ Icc qLo qHi,
      z * (activationPrimitive phi (1-z+q)-activationPrimitive phi q) / (lam-q) ≤ Y z := by
  intro z hz q hq
  have hL0 : 0 < lam := by linarith [hL.1]
  have hL1 : lam < 1 := by linarith [hL.2]
  have hz' : z ∈ Ioo (0 : ℝ) 1 := by
    norm_num [zTest,zEnd] at hz
    constructor <;> linarith [hz.1,hz.2]
  have hq0 : 0 ≤ q := by norm_num [qLo,qHi] at hq; linarith [hq.1]
  have hqz : q ≤ z := by norm_num [qLo,qHi] at hq; norm_num [zTest,zEnd] at hz; linarith [hq.2,hz.1]
  have hqL : q < lam := by norm_num [qLo,qHi] at hq; linarith [hq.2,hL.1]
  have hb := h.toNormalizedNecessaryTwoClass.two_class_all hL0 hL1 z q hz' hq0 hqz hqL.le
  have hinc := hY z ⟨by norm_num [zStart,zTest,zEnd] at *; linarith [hz.1],hz.2⟩
  apply (div_le_iff₀ (sub_pos.mpr hqL)).mpr
  have hm := mul_le_mul_of_nonneg_left hinc (sub_nonneg.mpr hqL.le)
  linarith

end NormalizedNecessaryConditions
end OptimalG
