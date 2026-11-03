import OptimalG.FirstPhaseComparison
import OptimalG.InitialSignedContinuation

/-! The first concrete relocated rational field and its essential-infimum comparison. -/
namespace OptimalG.Relocation
open Set MeasureTheory Variational
open scoped NNReal

private theorem control_boxes {c : Control} (hc : c ∈ controlDomain) :
    c.1 ∈ Icc (0.25 : ℝ) 0.36 ∧ c.2.1 ∈ Icc (0.285 : ℝ) 0.38 ∧
      c.2.2 ∈ Icc (0.285 : ℝ) 0.38 := by
  have hyl := (le_max_left xLo c.1).trans hc.2.2.1
  refine ⟨?_,?_,?_⟩
  · convert hc.1 using 1 <;> norm_num [pLo,pHi]
  · convert hc.2.1 using 1 <;> norm_num [xLo,xHi]
  · convert (show c.2.2 ∈ Icc xLo xHi from ⟨hyl,hc.2.2.2⟩) using 1 <;> norm_num [xLo,xHi]

theorem first_raw_determinant {lam : ℝ} {phi : ℝ → ℝ}
    (h : NormalizedNecessaryTwoClass lam phi) (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {c : Control} (hc : c ∈ controlDomain) :
    (0.0519 : ℝ) ≤ rawDet lam (firstExtendedPrimitive lam phi) c := by
  obtain ⟨hp,hx,hy⟩ := control_boxes hc
  obtain ⟨hm1,hm2,hmt⟩ := mass_budget h hL hLP
  have hmu : massOne lam phi ≤ (0.00025509854 : ℝ) := by linarith
  have heta : prefixGain lam phi ∈ Icc (0 : ℝ) (2.98*0.00025509854) :=
    ⟨mul_nonneg (by norm_num) hm1,mul_le_mul_of_nonneg_left hmu (by norm_num)⟩
  have hb := h.bounded_slack_phase_boxes hL hLP hp hx hy heta ⟨hm1,hmu⟩
  unfold rawDet
  rw [firstExtended_eq lam phi ⟨by linarith [hp.1],by linarith [hp.2]⟩,
    firstExtended_eq lam phi ⟨by linarith [hp.2],by linarith [hp.1]⟩,
    (first_RP_increments h hL hLP hp).1,(first_RP_increments h hL hLP hp).2]
  exact hb.2.2.1.le

theorem first_raw_regular {lam : ℝ} {phi : ℝ → ℝ}
    (h : NormalizedNecessaryConditions lam phi) (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) :
    ∃ K : ℝ≥0, (∀ z, LipschitzWith K (rawVectorField lam (firstExtendedPrimitive lam phi) phi z)) ∧
      ∀ u, Continuous (fun z => rawVectorField lam (firstExtendedPrimitive lam phi) phi z u) := by
  obtain ⟨K,hK⟩ := firstExtended_lipschitz h.toNormalizedNecessaryTwoClass
  have hs := h.initial_raw_scores_bounded
  exact rawVectorField_regular hK (by norm_num : (0 : ℝ) < 0.0519)
    (fun c hc => first_raw_determinant h.toNormalizedNecessaryTwoClass hL hLP hc) hs.1 hs.2

theorem first_raw_field_comparison {lam : ℝ} {phi : ℝ → ℝ}
    (h : NormalizedNecessaryConditions lam phi) (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {z Y err : ℝ}
    (hz : z ∈ Icc zStart zEnd)
    (hYlo : linePrimitive lam z-linePrimitive lam 1 ≤ Y)
    (hYhi : Y ≤ linePrimitive lam z-slack lam phi zStart)
    (he : err ∈ Icc (0 : ℝ) (0.784*massOne lam phi)) :
    rawVectorField lam (extendedPrimitive phi) phi z Y-(6.19*massOne lam phi+4.53*err) ≤
      rawVectorField lam (firstExtendedPrimitive lam phi) phi z
        (Y+prefixGain lam phi+massOne lam phi-err) := by
  obtain ⟨K0,hK0⟩ := extendedPrimitive_lipschitz h.continuous
  obtain ⟨K1,hK1⟩ := firstExtended_lipschitz h.toNormalizedNecessaryTwoClass
  have hs := h.initial_raw_scores_bounded
  have hb0 := raw_coefficients_bounded hK0 (by norm_num : (0 : ℝ) < 0.0535)
    (h.initial_raw_determinant hL hLP) hs.1 hs.2
  have hb1 := raw_coefficients_bounded hK1 (by norm_num : (0 : ℝ) < 0.0519)
    (fun c hc => first_raw_determinant h.toNormalizedNecessaryTwoClass hL hLP hc) hs.1 hs.2
  have hf0 := signedControlH_bounded (lam := lam) hK0 hb0.1 hb0.2 control_coordinates_bounded.1 z Y
  have hf1 := signedControlH_bounded (lam := lam) hK1 hb1.1 hb1.2 control_coordinates_bounded.1 z
    (Y+prefixGain lam phi+massOne lam phi-err)
  have herr0 := he.1
  apply clipped_essInf_comparison (by
    have hm := (mass_budget h.toNormalizedNecessaryTwoClass hL hLP).1
    positivity) hf0 hf1
  have hm : ∀ᵐ c ∂controlMeasure, c ∈ controlDomain := ae_restrict_mem controlDomain_measurable
  filter_upwards [hm] with c hc
  have hz' : z ∈ Icc (0.775 : ℝ) 0.875 := by convert hz using 1 <;> norm_num [zStart,zEnd]
  have hYhi' : Y ≤ linePrimitive lam z-slack lam phi 0.775 := by
    convert hYhi using 1 <;> norm_num [zStart]
  exact first_raw_control_comparison h.toNormalizedNecessaryTwoClass hL hLP hc hz' hYlo hYhi' he

end OptimalG.Relocation
