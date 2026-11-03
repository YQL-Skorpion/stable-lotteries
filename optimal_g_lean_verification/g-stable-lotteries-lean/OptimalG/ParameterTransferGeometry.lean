import OptimalG.ParameterTransferBoxes
import OptimalG.PhaseStateGeometry

/-! The actual upward-shifted variational data satisfy all seven phase
geometry inequalities, including the interpolated high-state bounds. -/
namespace OptimalG.Variational.ParameterTransfer
open Set

theorem control_ranges {c : Control} (hc : c ∈ controlDomain) :
    c.1 ∈ Icc (0.25 : ℝ) 0.36 ∧ c.2.1 ∈ Icc (0.285 : ℝ) 0.38 ∧
      c.2.2 ∈ Icc (0.285 : ℝ) 0.38 := by
  have hy : c.2.2 ∈ Icc xLo xHi := ⟨(le_max_left _ _).trans hc.2.2.1,hc.2.2.2⟩
  refine ⟨?_,?_,?_⟩
  · convert! hc.1 using 1 <;> norm_num [pLo,pHi]
  · convert! hc.2.1 using 1 <;> norm_num [xLo,xHi]
  · convert! hy using 1 <;> norm_num [xLo,xHi]

theorem admissible_RP_boxes {lam delta t : ℝ} {d : LowRankData}
    (h : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hd : 0 ≤ delta) {c : Control} (hc : c ∈ controlDomain) (ht : t ∈ Icc (0 : ℝ) 1) :
    let R := primitive lam d c.1+t*(0.1788*delta)
    let P := quadratic lam (1-c.1)-d.S+t*(0.1788*delta+delta*(0.62-c.1))
    R ∈ Icc (0.0826 : ℝ) 0.136 ∧ 0 ≤ P ∧
      0.0519 < Certificates.Control.det (2*(lam+delta)-c.2.1) (c.1+c.2.2-(lam+delta)) R P ∧
      0 < (lam+delta)*R-c.1*P ∧ (1-c.1)*R ≤ (lam+delta)*P := by
  obtain ⟨hp,hx,hy⟩ := control_ranges hc
  have hL := h.compact_lambdaRange
  have hdmax : delta ≤ (0.000005 : ℝ) := by linarith [hL.1,hLnew.2]
  have htd := mul_le_mul_of_nonneg_right ht.2 hd
  have hRb : (0.0826 : ℝ) ≤ primitive lam d c.1 := by
    convert! h.control_R_lower hc.1 using 1 <;> norm_num
  have hPb : quadratic lam (1-c.1)-d.S ∈ Icc (0 : ℝ) 0.159 := by
    convert! h.control_P_bounds hc.1 using 1 <;> norm_num
  have hh := phase_RP_boxes hL hLnew ⟨hd,hdmax⟩
    (s := t*delta) ⟨mul_nonneg ht.1 hd,by simpa only [one_mul] using htd⟩ hp hx hy
    ⟨hRb,(Admissible_control_R_small h hc.1).le⟩
    hPb (h.determinant_sharp hc) (h.control_binary_gap hc)
    (Admissible_complement_binary h hc.1)
  convert! hh using 1 <;> ring

theorem phase_K_bounds {lam delta p z Y t err S : ℝ}
    (hLnew : Certificates.Compact.LambdaRange (lam+delta)) (hd : 0 ≤ delta) (hS : 0 ≤ S)
    (hp : p ∈ Icc (0.25 : ℝ) 0.36) (hz : z ∈ Icc (0.775 : ℝ) 0.875)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hYlo : quadratic lam z-quadratic lam 1 ≤ Y)
    (hYhi : Y ≤ quadratic lam z-S)
    (he : err ∈ Icc (0 : ℝ) (0.784*(0.395*delta))) :
    0 < quadratic lam (z-p)-S-Y+t*(delta*(z-p-0.38)-0.395*delta+err) ∧
      quadratic lam (z-p)-S-Y+t*(delta*(z-p-0.38)-0.395*delta+err) < 0.111315 := by
  let base := fun r : ℝ => S+delta*r
  let target := fun _ : ℝ => scalar S delta
  have hb : Monotone base := fun a b hab => add_le_add le_rfl (mul_le_mul_of_nonneg_left hab hd)
  have htarget : Monotone target := monotone_const
  have hbn : 0 ≤ base (z-p) := by
    dsimp [base]
    exact add_nonneg hS (mul_nonneg hd (by linarith [hz.1,hp.2]))
  have htn : 0 ≤ target (z-p) := by dsimp [target,scalar]; positivity
  have hstart : target 0.775=base 0.775-0.5738*delta := by dsimp [target,base,scalar]; ring
  have hlo : linePrimitive (lam+delta) z-linePrimitive (lam+delta) 1 ≤ Y := by
    have hh := mul_nonpos_of_nonneg_of_nonpos hd (show z-1 ≤ 0 by linarith [hz.2])
    unfold linePrimitive quadratic at *
    nlinarith only [hYlo,hh]
  have hhi : Y ≤ linePrimitive (lam+delta) z-base 0.775 := by
    have hh := mul_nonneg hd (show 0 ≤ z-0.775 by linarith [hz.1])
    dsimp [base]
    unfold linePrimitive quadratic at *
    nlinarith only [hYhi,hh]
  have hg : err ≤ 0.5738*delta := by linarith [he.2]
  have hh := interpolated_phase_gap hLnew hp hz ht hb htarget hbn htn hstart hlo hhi he.1 hg
  have heq : linePrimitive (lam+delta) (z-p)-mixedSlack base target t (z-p)-
      (Y+t*(0.5738*delta-err)) =
      quadratic lam (z-p)-S-Y+t*(delta*(z-p-0.38)-0.395*delta+err) := by
    dsimp [linePrimitive,quadratic,mixedSlack,base,target,scalar]
    ring
  simpa only [heq] using hh.2.2

theorem phase_geometry {lam delta z Y t err : ℝ} {d : LowRankData}
    (h : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hd : 0 ≤ delta) {c : Control} (hc : c ∈ controlDomain)
    (hz : z ∈ Icc (0.775 : ℝ) 0.875) (ht : t ∈ Icc (0 : ℝ) 1)
    (hYlo : quadratic lam z-quadratic lam 1 ≤ Y)
    (hYhi : Y ≤ quadratic lam z-d.S)
    (he : err ∈ Icc (0 : ℝ) (0.784*(0.395*delta))) :
    let R := primitive lam d c.1+t*(0.1788*delta)
    let P := quadratic lam (1-c.1)-d.S+t*(0.1788*delta+delta*(0.62-c.1))
    let K := quadratic lam (z-c.1)-d.S-Y+t*(delta*(z-c.1-0.38)-0.395*delta+err)
    R ∈ Icc (0.0826 : ℝ) 0.136 ∧ 0 ≤ P ∧ K ∈ Icc (0 : ℝ) 0.159 ∧
      0.0519 < Certificates.Control.det (2*(lam+delta)-c.2.1) (c.1+c.2.2-(lam+delta)) R P ∧
      0 < Certificates.Control.cx (z-(lam+delta)) (c.1+c.2.2-(lam+delta)) R K ∧
      0 < (lam+delta)*R-c.1*P ∧ (1-c.1)*R ≤ (lam+delta)*P := by
  obtain ⟨hp,hx,hy⟩ := control_ranges hc
  obtain ⟨hR,hP,hD,hB,hcomp⟩ := admissible_RP_boxes h hLnew hd hc ht
  have hK := phase_K_bounds hLnew hd (show 0 ≤ d.S by linarith [h.slack_lower]) hp hz ht hYlo hYhi he
  have hPbase := Certificates.Compact.complementary_primitive_floor lam d.S c.1
    h.compact_lambdaRange h.compact_scalarRange hp
  have hPg := mul_nonneg ht.1
    (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.1788) hd)
      (mul_nonneg hd (show 0 ≤ 0.62-c.1 by linarith [hp.2])))
  have hPfloor : 0.113 ≤ quadratic lam (1-c.1)-d.S+t*(0.1788*delta+delta*(0.62-c.1)) := by
    change 0.113 < quadratic lam (1-c.1)-d.S at hPbase
    linarith
  have hX := Certificates.Control.coefficients_positive (lam+delta) c.1 c.2.1 c.2.2 z _ _ _
    hLnew hp hx.2 hy.1 hz hR.1 hPfloor hK.1.le hK.2.le
  exact ⟨hR,hP,⟨hK.1.le,by linarith [hK.2]⟩,hD,by linarith [hX.1],hB,hcomp⟩

end OptimalG.Variational.ParameterTransfer
