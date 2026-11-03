import OptimalG.FirstPhaseGeometry
import OptimalG.RelocationBinary

/-! Complete interpolation geometry for the second slack-removal phase. -/
namespace OptimalG.Relocation
open Set

noncomputable def secondGain (lam : ℝ) (phi : ℝ → ℝ) (r : ℝ) : ℝ :=
  firstSlack lam phi r-secondSlack lam phi r

theorem second_primitive_increment (lam : ℝ) (phi : ℝ → ℝ) (r : ℝ) :
    secondPrimitive lam phi r=firstPrimitive lam phi r+secondGain lam phi r := by
  unfold secondPrimitive firstPrimitive secondGain
  ring

theorem second_start_slack {lam : ℝ} {phi : ℝ → ℝ}
    (h : NormalizedNecessaryTwoClass lam phi) (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) :
    secondSlack lam phi 0.775=firstSlack lam phi 0.775-massTwo lam phi := by
  rw [secondSlack_middle h hL hLP (by norm_num),first_after_eq h hL hLP (by norm_num)]
  unfold massOne massTwo
  ring

theorem second_phase_geometry {lam : ℝ} {phi : ℝ → ℝ}
    (h : NormalizedNecessaryTwoClass lam phi) (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p x y z Y t err : ℝ}
    (hp : p ∈ Icc (0.25 : ℝ) 0.36) (hx : x ∈ Icc (0.285 : ℝ) 0.38)
    (hy : y ∈ Icc (0.285 : ℝ) 0.38) (hz : z ∈ Icc (0.775 : ℝ) 0.875)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hYlo : linePrimitive lam z-linePrimitive lam 1 ≤ Y)
    (hYhi : Y ≤ linePrimitive lam z-firstSlack lam phi 0.775)
    (he : err ∈ Icc (0 : ℝ) (0.784*massTwo lam phi)) :
    let R := firstPrimitive lam phi p+t*0
    let P := firstPrimitive lam phi (1-p)+t*(0+secondGain lam phi (1-p))
    let K := firstPrimitive lam phi (z-p)-Y+
      t*(secondGain lam phi (z-p)-massTwo lam phi+err)
    R ∈ Icc (0.0826 : ℝ) 0.136 ∧ 0 ≤ P ∧ K ∈ Icc (0 : ℝ) 0.159 ∧
    0.0519 < Certificates.Control.det (2*lam-x) (p+y-lam) R P ∧
    0 < Certificates.Control.cx (z-lam) (p+y-lam) R K ∧
    0 < lam*R-p*P ∧ (1-p)*R ≤ lam*P := by
  obtain ⟨hm1,hm2,hmt⟩ := mass_budget h hL hLP
  have hmu : massOne lam phi ≤ (0.00025509854 : ℝ) := by linarith
  have heta : prefixGain lam phi ∈ Icc (0 : ℝ) (2.98*0.00025509854) :=
    ⟨mul_nonneg (by norm_num) hm1,mul_le_mul_of_nonneg_left hmu (by norm_num)⟩
  have hdp : secondGain lam phi (1-p) ∈ Icc (0 : ℝ) (massTwo lam phi) :=
    second_gain_bounds h hL hLP (1-p)
  have htdp : t*secondGain lam phi (1-p) ≤ massTwo lam phi :=
    (mul_le_mul_of_nonneg_right ht.2 hdp.1).trans (by simpa only [one_mul] using hdp.2)
  have hd : massOne lam phi+t*secondGain lam phi (1-p) ∈ Icc (0 : ℝ) 0.00025509854 :=
    ⟨add_nonneg hm1 (mul_nonneg ht.1 hdp.1),by linarith⟩
  have hb := h.bounded_slack_phase_boxes hL hLP hp hx hy heta hd
  have hRP := first_RP_increments h hL hLP hp
  have hR : (0.0826 : ℝ) < firstPrimitive lam phi p ∧ firstPrimitive lam phi p < 0.136 := by
    simpa only [hRP.1] using hb.1
  have hP : 0 < firstPrimitive lam phi (1-p)+t*secondGain lam phi (1-p) := by
    rw [hRP.2]
    linarith [hb.2.1.1]
  have hD : 0.0519 < Certificates.Control.det (2*lam-x) (p+y-lam)
      (firstPrimitive lam phi p) (firstPrimitive lam phi (1-p)+t*secondGain lam phi (1-p)) := by
    rw [hRP.1,hRP.2]
    unfold Certificates.Control.det
    nlinarith only [hb.2.2.1]
  have hB : 0 < lam*firstPrimitive lam phi p-p*(firstPrimitive lam phi (1-p)+t*secondGain lam phi (1-p)) := by
    rw [hRP.1,hRP.2]
    nlinarith only [hb.2.2.2]
  have herrGain : err ≤ massTwo lam phi := by linarith [he.2]
  have hgap := interpolated_phase_gap hL hp hz ht (first_monotone h hL hLP) (second_monotone h hL hLP)
    (firstSlack_nonneg h hL hLP (z-p)) (secondSlack_nonneg h hL hLP (z-p))
    (second_start_slack h hL hLP) hYlo hYhi he.1 herrGain
  have heq : linePrimitive lam (z-p)-mixedSlack (firstSlack lam phi) (secondSlack lam phi) t (z-p)-
      (Y+t*(massTwo lam phi-err)) = firstPrimitive lam phi (z-p)-Y+
      t*(secondGain lam phi (z-p)-massTwo lam phi+err) := by
    unfold mixedSlack secondGain firstPrimitive
    ring
  have hK : 0 < firstPrimitive lam phi (z-p)-Y+t*(secondGain lam phi (z-p)-massTwo lam phi+err) ∧
      firstPrimitive lam phi (z-p)-Y+t*(secondGain lam phi (z-p)-massTwo lam phi+err) < 0.111315 := by
    simpa only [heq] using hgap.2.2
  have hX := (phase_control_coefficients_positive hL hp hx hy hz hR.1 hP hK).1
  have hcomp := first_complement_binary h hL hLP (p := p) ⟨hp.1,by linarith [hp.2]⟩
  have hadd : 0 ≤ lam*(t*secondGain lam phi (1-p)) :=
    mul_nonneg (by linarith [hL.1]) (mul_nonneg ht.1 hdp.1)
  simp only [mul_zero,add_zero,zero_add]
  refine ⟨⟨hR.1.le,hR.2.le⟩,hP.le,⟨hK.1.le,by linarith [hK.2]⟩,hD,?_,hB,?_⟩
  · unfold Certificates.Control.cx
    linarith
  · nlinarith only [hcomp,hadd]

end OptimalG.Relocation
