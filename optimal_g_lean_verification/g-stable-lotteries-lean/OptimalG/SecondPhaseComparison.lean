import OptimalG.SecondPhaseGeometry
import OptimalG.FirstPhaseField
import OptimalG.SecondRawControl

/-! Signed clipped-control and essential-infimum comparison for the second phase. -/
namespace OptimalG.Relocation
open Set MeasureTheory Variational
open scoped NNReal

theorem second_control_comparison {lam : ℝ} {phi : ℝ → ℝ}
    (h : NormalizedNecessaryTwoClass lam phi) (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p x y z Y err : ℝ}
    (hp : p ∈ Icc (0.25 : ℝ) 0.36) (hx : x ∈ Icc (0.285 : ℝ) 0.38)
    (hy : y ∈ Icc (0.285 : ℝ) 0.38) (hpy : p ≤ y)
    (hz : z ∈ Icc (0.775 : ℝ) 0.875)
    (hYlo : linePrimitive lam z-linePrimitive lam 1 ≤ Y)
    (hYhi : Y ≤ linePrimitive lam z-firstSlack lam phi 0.775)
    (he : err ∈ Icc (0 : ℝ) (0.784*massTwo lam phi)) :
    min (lam-z) (Certificates.Control.value (z-lam) (2*lam-x) (p+y-lam)
      (firstPrimitive lam phi p) (firstPrimitive lam phi (1-p))
      (firstPrimitive lam phi (z-p)-Y) (phi x) (phi y)) -
        (6.19*massTwo lam phi+4.53*err) ≤
    min (lam-z) (Certificates.Control.value (z-lam) (2*lam-x) (p+y-lam)
      (secondPrimitive lam phi p) (secondPrimitive lam phi (1-p))
      (secondPrimitive lam phi (z-p)-(Y+massTwo lam phi-err)) (phi x) (phi y)) := by
  have hm := (mass_budget h hL hLP).2.1
  have hdp := (second_gain_bounds h hL hLP (1-p)).2
  have hdk := (second_gain_bounds h hL hLP (z-p)).2
  have hU : z-lam ∈ Icc (0.21267 : ℝ) 0.313 :=
    ⟨by linarith [hz.1,hL.2],by linarith [hz.2,hL.1]⟩
  have hh := Certificates.Control.phaseValue_clipped_of_geometry hL hp hx hy hpy hU
    (h.ceiling x ⟨by linarith [hx.1],by linarith [hx.2]⟩)
    (h.ceiling y ⟨by linarith [hy.1],by linarith [hy.2]⟩)
    (show (0 : ℝ) ≤ 0 from le_rfl) hm he.1 (dp := secondGain lam phi (1-p)) (dk := secondGain lam phi (z-p)) hdp hdk
    (fun t ht => second_phase_geometry h hL hLP hp hx hy hz ht hYlo hYhi he)
  simp only [mul_zero,add_zero,zero_add] at hh
  have hsame : secondPrimitive lam phi p=firstPrimitive lam phi p := by
    rw [secondPrimitive,firstPrimitive,second_low_eq h hL hLP (by linarith [hp.2])]
  have hK : firstPrimitive lam phi (z-p)-Y+secondGain lam phi (z-p)-massTwo lam phi+err =
      secondPrimitive lam phi (z-p)-(Y+massTwo lam phi-err) := by
    rw [second_primitive_increment]
    ring
  rw [hK,show -(z-lam)=lam-z by ring] at hh
  rw [hsame,second_primitive_increment lam phi (1-p)]
  exact hh

theorem second_raw_control_comparison {lam : ℝ} {phi : ℝ → ℝ}
    (h : NormalizedNecessaryTwoClass lam phi) (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {c : Control} {z Y err : ℝ}
    (hc : c ∈ controlDomain) (hz : z ∈ Icc (0.775 : ℝ) 0.875)
    (hYlo : linePrimitive lam z-linePrimitive lam 1 ≤ Y)
    (hYhi : Y ≤ linePrimitive lam z-firstSlack lam phi 0.775)
    (he : err ∈ Icc (0 : ℝ) (0.784*massTwo lam phi)) :
    min (lam-z) (signedControlH lam (firstExtendedPrimitive lam phi)
      (rawAlpha lam (firstExtendedPrimitive lam phi) phi)
      (rawBeta lam (firstExtendedPrimitive lam phi) phi) (·.1) z Y c) -
        (6.19*massTwo lam phi+4.53*err) ≤
    min (lam-z) (signedControlH lam (secondExtendedPrimitive lam phi)
      (rawAlpha lam (secondExtendedPrimitive lam phi) phi)
      (rawBeta lam (secondExtendedPrimitive lam phi) phi) (·.1) z (Y+massTwo lam phi-err) c) := by
  have hp : c.1 ∈ Icc (0.25 : ℝ) 0.36 := by
    convert hc.1 using 1 <;> norm_num [pLo,pHi]
  have hx : c.2.1 ∈ Icc (0.285 : ℝ) 0.38 := by
    convert hc.2.1 using 1 <;> norm_num [xLo,xHi]
  have hyl := (le_max_left xLo c.1).trans hc.2.2.1
  have hy : c.2.2 ∈ Icc (0.285 : ℝ) 0.38 := by
    convert (show c.2.2 ∈ Icc xLo xHi from ⟨hyl,hc.2.2.2⟩) using 1 <;> norm_num [xLo,xHi]
  have hpy := (le_max_right xLo c.1).trans hc.2.2.1
  have hpI : c.1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hp.1],by linarith [hp.2]⟩
  have hpcI : 1-c.1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hp.2],by linarith [hp.1]⟩
  have hrI : z-c.1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hz.1,hp.2],by linarith [hz.2,hp.1]⟩
  rw [rawControl_eq_value,rawControl_eq_value,
    firstExtended_eq lam phi hpI,firstExtended_eq lam phi hpcI,firstExtended_eq lam phi hrI,
    secondExtended_eq lam phi hpI,secondExtended_eq lam phi hpcI,secondExtended_eq lam phi hrI]
  exact second_control_comparison h hL hLP hp hx hy hpy hz hYlo hYhi he

theorem second_raw_field_comparison {lam : ℝ} {phi : ℝ → ℝ}
    (h : NormalizedNecessaryConditions lam phi) (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {z Y err : ℝ}
    (hz : z ∈ Icc zStart zEnd)
    (hYlo : linePrimitive lam z-linePrimitive lam 1 ≤ Y)
    (hYhi : Y ≤ linePrimitive lam z-firstSlack lam phi zStart)
    (he : err ∈ Icc (0 : ℝ) (0.784*massTwo lam phi)) :
    rawVectorField lam (firstExtendedPrimitive lam phi) phi z Y-(6.19*massTwo lam phi+4.53*err) ≤
      rawVectorField lam (secondExtendedPrimitive lam phi) phi z (Y+massTwo lam phi-err) := by
  obtain ⟨K0,hK0⟩ := firstExtended_lipschitz h.toNormalizedNecessaryTwoClass
  obtain ⟨K1,hK1⟩ := secondExtended_lipschitz h.toNormalizedNecessaryTwoClass
  have hs := h.initial_raw_scores_bounded
  have hb0 := raw_coefficients_bounded hK0 (by norm_num : (0 : ℝ) < 0.0519)
    (fun c hc => first_raw_determinant h.toNormalizedNecessaryTwoClass hL hLP hc) hs.1 hs.2
  have hb1 := raw_coefficients_bounded hK1 (by norm_num : (0 : ℝ) < 0.0519)
    (second_raw_determinant h.toNormalizedNecessaryTwoClass hL hLP) hs.1 hs.2
  have hf0 := signedControlH_bounded (lam := lam) hK0 hb0.1 hb0.2 control_coordinates_bounded.1 z Y
  have hf1 := signedControlH_bounded (lam := lam) hK1 hb1.1 hb1.2 control_coordinates_bounded.1 z
    (Y+massTwo lam phi-err)
  have herr0 := he.1
  apply clipped_essInf_comparison (by
    have hm := (mass_budget h.toNormalizedNecessaryTwoClass hL hLP).2.1
    positivity) hf0 hf1
  have hm : ∀ᵐ c ∂controlMeasure, c ∈ controlDomain := ae_restrict_mem controlDomain_measurable
  filter_upwards [hm] with c hc
  have hz' : z ∈ Icc (0.775 : ℝ) 0.875 := by convert hz using 1 <;> norm_num [zStart,zEnd]
  have hYhi' : Y ≤ linePrimitive lam z-firstSlack lam phi 0.775 := by
    convert hYhi using 1 <;> norm_num [zStart]
  exact second_raw_control_comparison h.toNormalizedNecessaryTwoClass hL hLP hc hz' hYlo hYhi' he

end OptimalG.Relocation
