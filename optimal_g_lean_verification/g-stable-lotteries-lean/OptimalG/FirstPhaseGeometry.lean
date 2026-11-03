import OptimalG.RelocationRegularity
import OptimalG.PhaseStateGeometry
import OptimalG.PhaseBinaryComparison

/-! Numerical and binary domains along the actual first-phase interpolation. -/
namespace OptimalG.Relocation
open Set

noncomputable def firstMiddleGain (lam : ℝ) (phi : ℝ → ℝ) (r : ℝ) : ℝ :=
  slack lam phi r-firstSlack lam phi r-prefixGain lam phi

theorem first_phase_geometry {lam : ℝ} {phi : ℝ → ℝ}
    (h : NormalizedNecessaryTwoClass lam phi) (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p x y z Y t err : ℝ}
    (hp : p ∈ Icc (0.25 : ℝ) 0.36) (hx : x ∈ Icc (0.285 : ℝ) 0.38)
    (hy : y ∈ Icc (0.285 : ℝ) 0.38) (hz : z ∈ Icc (0.775 : ℝ) 0.875)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hYlo : linePrimitive lam z-linePrimitive lam 1 ≤ Y)
    (hYhi : Y ≤ linePrimitive lam z-slack lam phi 0.775)
    (he : err ∈ Icc (0 : ℝ) (0.784*massOne lam phi)) :
    let R := activationPrimitive phi p+t*prefixGain lam phi
    let P := activationPrimitive phi (1-p)+t*(prefixGain lam phi+massOne lam phi)
    let K := activationPrimitive phi (z-p)-Y+
      t*(firstMiddleGain lam phi (z-p)-massOne lam phi+err)
    R ∈ Icc (0.0826 : ℝ) 0.136 ∧ 0 ≤ P ∧ K ∈ Icc (0 : ℝ) 0.159 ∧
    0.0519 < Certificates.Control.det (2*lam-x) (p+y-lam) R P ∧
    0 < Certificates.Control.cx (z-lam) (p+y-lam) R K ∧
    0 < lam*R-p*P ∧ (1-p)*R ≤ lam*P := by
  obtain ⟨hm1,hm2,hmt⟩ := mass_budget h hL hLP
  have hmu : massOne lam phi ≤ (0.00025509854 : ℝ) := by linarith
  have heta : 0 ≤ prefixGain lam phi := mul_nonneg (by norm_num) hm1
  have htm := mul_le_mul_of_nonneg_right ht.2 hm1
  have hte := mul_le_mul_of_nonneg_right ht.2 heta
  have hetaHi : prefixGain lam phi ≤ 2.98*0.00025509854 :=
    mul_le_mul_of_nonneg_left hmu (by norm_num)
  have hbox := h.bounded_slack_phase_boxes hL hLP hp hx hy
    (eta := t*prefixGain lam phi) (delta := t*massOne lam phi)
    ⟨mul_nonneg ht.1 heta, hte.trans (by simpa only [one_mul] using hetaHi)⟩
    ⟨mul_nonneg ht.1 hm1, htm.trans (by simpa only [one_mul] using hmu)⟩
  have hR : (0.0826 : ℝ) < activationPrimitive phi p+t*prefixGain lam phi ∧
      activationPrimitive phi p+t*prefixGain lam phi < 0.136 := hbox.1
  have hP : 0 < activationPrimitive phi (1-p)+t*(prefixGain lam phi+massOne lam phi) ∧
      activationPrimitive phi (1-p)+t*(prefixGain lam phi+massOne lam phi) < 0.135 := by
    constructor <;> nlinarith only [hbox.2.1.1,hbox.2.1.2]
  have hD : 0.0519 < Certificates.Control.det (2*lam-x) (p+y-lam)
      (activationPrimitive phi p+t*prefixGain lam phi)
      (activationPrimitive phi (1-p)+t*(prefixGain lam phi+massOne lam phi)) := by
    unfold Certificates.Control.det
    nlinarith only [hbox.2.2.1]
  have hB : 0 < lam*(activationPrimitive phi p+t*prefixGain lam phi)-
      p*(activationPrimitive phi (1-p)+t*(prefixGain lam phi+massOne lam phi)) := by
    nlinarith only [hbox.2.2.2]
  have hstart : firstSlack lam phi 0.775 = slack lam phi 0.775-
      (prefixGain lam phi+massOne lam phi) := by
    rw [first_after_eq h hL hLP (by norm_num : (0.44 : ℝ) ≤ 0.775)]
    ring
  have herrGain : err ≤ prefixGain lam phi+massOne lam phi := by linarith [he.2]
  have hgap := interpolated_phase_gap hL hp hz ht (slack_monotone h) (first_monotone h hL hLP)
    (slack_nonneg h (z-p)) (firstSlack_nonneg h hL hLP (z-p)) hstart hYlo hYhi he.1 herrGain
  have hr : z-p ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hz.1,hp.2],by linarith [hz.2,hp.1]⟩
  have heq : linePrimitive lam (z-p)-mixedSlack (slack lam phi) (firstSlack lam phi) t (z-p)-
      (Y+t*(prefixGain lam phi+massOne lam phi-err)) =
      activationPrimitive phi (z-p)-Y+t*(firstMiddleGain lam phi (z-p)-massOne lam phi+err) := by
    unfold mixedSlack firstMiddleGain
    rw [slack_eq lam phi hr]
    unfold cumulativeSlack
    ring
  have hK : 0 < activationPrimitive phi (z-p)-Y+
      t*(firstMiddleGain lam phi (z-p)-massOne lam phi+err) ∧
      activationPrimitive phi (z-p)-Y+t*(firstMiddleGain lam phi (z-p)-massOne lam phi+err) < 0.111315 := by
    simpa only [heq] using hgap.2.2
  have hX := (phase_control_coefficients_positive hL hp hx hy hz hR.1 hP.1 hK).1
  have hL0 : 0 < lam := by linarith [hL.1]
  have hL1 : lam < 1 := by linarith [hL.2]
  have hpI : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1],by linarith [hp.2]⟩
  have hcI : 1-p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.2],by linarith [hp.1]⟩
  have hb := h.two_class_all hL0 hL1 (1-p) 0 hcI le_rfl hcI.1.le hL0.le
  have hb' := h.two_class_all hL0 hL1 p 0 hpI le_rfl hpI.1.le hL0.le
  have hcomp : (1-p)*activationPrimitive phi p ≤ lam*activationPrimitive phi (1-p) := by
    simpa only [sub_sub_cancel,add_zero,activationPrimitive,intervalIntegral.integral_same,sub_zero] using hb
  have hopp : p*activationPrimitive phi (1-p) ≤ lam*activationPrimitive phi p := by
    simpa only [add_zero,activationPrimitive,intervalIntegral.integral_same,sub_zero] using hb'
  have hpres := (first_phase_preserves_binary hL ⟨hp.1,by linarith [hp.2]⟩ hm1 ht.1 hcomp hopp).1
  refine ⟨⟨hR.1.le,hR.2.le⟩,hP.1.le,⟨hK.1.le,by linarith [hK.2]⟩,hD,?_,hB,?_⟩
  · unfold Certificates.Control.cx
    linarith
  · simpa only [prefixGain] using hpres

end OptimalG.Relocation
