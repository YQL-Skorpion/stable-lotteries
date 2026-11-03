import OptimalG.Certificates.StaticLayerSupport
import OptimalG.Certificates.StaticLowSemantic
import OptimalG.Certificates.LayerControl
import OptimalG.Certificates.StaticLayerInterpolation

/-! Whole-cell bounds for the actual variational control. -/
namespace OptimalG.Variational
open Set Certificates
open Certificates.StaticLow (lam slack)

theorem StaticLayerCell.lower_controlH {c : Certificates.StaticSupport.ContinuousLayerCell}
    (hg : c.geometryCheck=true) (hn : c.fastNumericCheck=true)
    {t : ℝ} (ht : t∈Ioo 0 1) {x y z u : ℝ}
    (hc : (c.pPoly.eval t,x,y)∈controlDomain) (hz : z∈Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1≤u)
    (huHigh : u≤quadratic lam z-slack) :
    -(z-(lam:ℝ))*c.Cu.eval t+c.alphau.eval t*(u-quadratic lam (z-c.pPoly.eval t)+slack)≤
      controlH lam staticLowData z u (c.pPoly.eval t,x,y) := by
  have had := staticLow_admissible
  have hpEnd : c.pPoly.eval t≤tEnd := by
    have hh := hc.1.2
    norm_num [pHi,tEnd] at hh ⊢
    linarith
  have hR : StaticLow.primitive (c.pPoly.eval t)=primitive lam staticLowData (c.pPoly.eval t) :=
    (primitive_staticLow (c.pPoly.eval t)).symm
  have hK := had.control_K_bounds hc.1 hz huLow huHigh
  have hcoeff := had.control_coefficients_positive hc hz huLow huHigh
  have hdet := had.determinant_positive hc
  dsimp only [staticLowData,Prod.fst,Prod.snd] at hK hcoeff hdet
  have hx0 : (0.2635:ℝ)≤x := by
    have hh := hc.2.1.1
    norm_num [xLo] at hh
    linarith
  have hy0 : (0.2635:ℝ)≤y := by
    have hh := (le_max_left xLo (c.pPoly.eval t)).trans hc.2.2.1
    norm_num [xLo] at hh
    linarith
  have hyp : c.pPoly.eval t≤y := (le_max_right xLo (c.pPoly.eval t)).trans hc.2.2.1
  have hU : 0≤z-(lam:ℝ) := by
    have hh := hz.1
    norm_num [zStart,lam] at hh ⊢
    linarith
  have hD : 0<Certificates.Control.det (2*(lam:ℝ)-x) (c.pPoly.eval t+y-lam)
      (StaticLow.primitive (c.pPoly.eval t)) (quadratic lam (1-c.pPoly.eval t)-slack) := by
    rw [hR]
    change (3/100:ℝ)<Certificates.Control.det (2*(lam:ℝ)-x) (c.pPoly.eval t+y-lam)
      (primitive lam staticLowData (c.pPoly.eval t)) (quadratic lam (1-c.pPoly.eval t)-slack) at hdet
    linarith
  have hcx : 0≤Certificates.Control.cx (z-lam) (c.pPoly.eval t+y-lam)
      (StaticLow.primitive (c.pPoly.eval t)) (quadratic lam (z-c.pPoly.eval t)-slack-u) := by
    rw [hR]
    have hh := hcoeff.1
    change (0.0145:ℝ)<Certificates.Control.cx (z-lam) (c.pPoly.eval t+y-lam)
      (primitive lam staticLowData (c.pPoly.eval t)) (quadratic lam (z-c.pPoly.eval t)-slack-u) at hh
    linarith only [hh]
  have hcy : 0≤Certificates.Control.cy (z-lam) (2*(lam:ℝ)-x)
      (quadratic lam (1-c.pPoly.eval t)-slack) (quadratic lam (z-c.pPoly.eval t)-slack-u) := by
    have hh := hcoeff.2
    linarith
  have hb := Certificates.StaticSupport.ContinuousLayerCell.checked_lower hg hn ht hU hK.1 hx0 hy0 hyp hD hcx hcy
  rw [hR] at hb
  rw [controlH_eq_certified_value lam staticLowData z u (c.pPoly.eval t,x,y)]
  change _≤Certificates.Control.value (z-lam) (2*(lam:ℝ)-x) (c.pPoly.eval t+y-lam)
    (primitive lam staticLowData (c.pPoly.eval t)) (quadratic lam (1-c.pPoly.eval t)-slack)
    (quadratic lam (z-c.pPoly.eval t)-slack-u) (StaticLow.score x) (StaticLow.score y)
  dsimp only [quadratic,Certificates.quadratic] at hb ⊢
  convert hb using 1 <;> ring


/-- The checked node fields control every intermediate layer, with the same
exact penalty that was used in the explicit high-curve residual certificates. -/
theorem StaticLayerCell.node_fields_lower_controlH {c : Certificates.StaticSupport.ContinuousLayerCell}
    (hg : c.geometryCheck=true) (hn : c.fastNumericCheck=true)
    {t : ℝ} (ht : t∈Ioo 0 1) {x y z u : ℝ}
    (hc : (c.pPoly.eval t,x,y)∈controlDomain) (hz : z∈Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1≤u)
    (huHigh : u≤quadratic lam z-slack) :
    min (coefficientField lam slack z u c.left.p c.left.Cu c.left.alphau)
      (coefficientField lam slack z u c.right.p c.right.Cu c.right.alphau)-1/10000000≤
      controlH lam staticLowData z u (c.pPoly.eval t,x,y) := by
  rcases (Certificates.StaticSupport.ContinuousLayerCell.geometry_parts hg).1 with
    ⟨_,_,_,hlow,hup,hpos,hgap,ha,hda⟩
  let h : ℝ := (c.right.p:ℝ)-c.left.p
  let w : ℝ := (c.pPoly.eval t-c.left.p)/h
  let da : ℝ := ((c.right.alphau:ℝ)-c.left.alphau)/h
  have hp : (0:ℝ)<h := by dsimp [h]; exact_mod_cast sub_pos.mpr hpos
  have hh : h∈Icc 0 (3/10000:ℝ) := by
    refine ⟨hp.le,?_⟩
    have hh' : ((c.right.p-c.left.p:ℚ):ℝ)≤((3/10000:ℚ):ℝ) := Rat.cast_le.mpr hgap
    norm_num at hh' ⊢
    dsimp [h]
    linarith only [hh']
  have hparam := (Certificates.StaticSupport.ContinuousLayerCell.geometry_parameter_bounds hg ⟨ht.1.le,ht.2.le⟩).1
  have hw : w∈Icc 0 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr hparam.1) hp.le,?_⟩
    apply (div_le_iff₀ hp).mpr
    dsimp [h]
    linarith [hparam.2]
  have ha' : (c.left.alphau:ℝ)≤3 := by exact_mod_cast ha
  have hda' : |da|≤2 := by dsimp [da,h]; exact_mod_cast hda
  have hk : |z-(c.left.p:ℝ)-lam|≤1 := by
    have hlo : (1/4:ℝ)≤c.left.p := by
      have hh' : ((1/4:ℚ):ℝ)≤c.left.p := Rat.cast_le.mpr hlow
      norm_num at hh' ⊢
      exact hh'
    have hhi : (c.right.p:ℝ)≤9/25 := by
      have hh' : (c.right.p:ℝ)≤((9/25:ℚ):ℝ) := Rat.cast_le.mpr hup
      norm_num at hh' ⊢
      exact hh'
    have hpr : (c.left.p:ℝ)<c.right.p := by exact_mod_cast hpos
    have hz' := hz
    apply abs_le.mpr
    norm_num [zStart,zEnd,lam] at hz' ⊢
    constructor <;> linarith [hz'.1,hz'.2]
  have hU : z-(lam:ℝ)≤1/3 := by
    have hz' := hz.2
    norm_num [zEnd,lam] at hz' ⊢
    linarith
  have hK : quadratic lam (z-c.pPoly.eval t)-slack-u≤1/8 := by
    have hk' := staticLow_admissible.control_K_bounds hc.1 hz huLow huHigh
    dsimp only [staticLowData] at hk'
    linarith [hk'.2]
  have hpEnd : (c.left.p:ℝ)+h=c.right.p := by dsimp [h]; ring
  have haEnd : (c.left.alphau:ℝ)+da*h=c.right.alphau := by
    dsimp [da]
    rw [div_mul_cancel₀ _ hp.ne']
    try ring
  have hpMid : (c.left.p:ℝ)+h*w=c.pPoly.eval t := by
    dsimp [w]
    rw [mul_div_cancel₀ _ hp.ne']
    try ring
  have hCMid : (c.left.Cu:ℝ)+((c.right.Cu:ℝ)-c.left.Cu)*w+1/200000000=c.Cu.eval t := by
    rw [Certificates.StaticSupport.ContinuousLayerCell.Cu_eval]
  have haMid : (c.left.alphau:ℝ)+da*h*w+1/200000000=c.alphau.eval t := by
    dsimp only [da]
    rw [div_mul_cancel₀ _ hp.ne',Certificates.StaticSupport.ContinuousLayerCell.alphau_eval]
  have hK' : Certificates.quadratic lam (z-((c.left.p:ℝ)+h*w))-slack-u≤1/8 := by
    rw [hpMid]
    exact hK
  have hi := static_coefficientField_padded_lower hh hw ha' hda' hk hU hK'
    (C:=(c.left.Cu:ℝ)) (dC:=(c.right.Cu:ℝ)-c.left.Cu)
  rw [hpEnd,haEnd,hpMid,hCMid,haMid] at hi
  have hCEnd : (c.left.Cu:ℝ)+((c.right.Cu:ℝ)-c.left.Cu)=c.right.Cu := by ring
  rw [hCEnd] at hi
  exact hi.trans (StaticLayerCell.lower_controlH hg hn ht hc hz huLow huHigh)

end OptimalG.Variational
