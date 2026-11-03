import OptimalG.Certificates.LayerNode
import OptimalG.Certificates.VariationalBridge

/-! The layer checker lower-bounds the actual high-rank variational control. -/
namespace OptimalG.Variational
open Set Certificates
open Certificates.UpperProfileData

theorem upperTrial_primitive_eq {r : ℝ} (hr : r≤tEnd) :
    primitive lam upperTrialData r=UpperTrial.primitive r := by
  unfold primitive
  by_cases he : r≤ell
  · rw [if_pos he]
    have hc : r≤(leftContact:ℝ) := by
      have hh := UpperTrial.contact_range.1
      norm_num [ell] at he
      linarith
    change Certificates.cap lam slack r=
      if r≤leftContact then Certificates.cap lam slack r else cubicPrimitive lam slack pieces r
    rw [if_pos hc]
  · rw [if_neg he,if_pos hr,lowPrimitive_upperTrial]

/-- The finite node's verified lower field applies to every actual independent
root at that node, throughout the full high-state budget rectangle. -/
theorem LayerNode.lower_controlH {n : Certificates.LayerNode} (hn : n.check=true)
    {x y z u : ℝ} (hc : ((n.p:ℝ),x,y)∈controlDomain) (hz : z∈Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1≤u)
    (huHigh : u≤quadratic lam z-slack) :
    -(z-(lam:ℝ))*n.Cu+(n.alphau:ℝ)*(u-quadratic lam (z-n.p)+slack)≤
      controlH lam upperTrialData z u ((n.p:ℝ),x,y) := by
  have had := upperTrial_admissible
  have hpEnd : (n.p:ℝ)≤tEnd := by
    have hh := hc.1.2
    norm_num [pHi,tEnd] at hh ⊢
    linarith
  have hR : (n.R:ℝ)=primitive lam upperTrialData n.p := by
    rw [upperTrial_primitive_eq hpEnd]
    simp [Certificates.LayerNode.R]
  have hP : (n.P:ℝ)=quadratic lam (1-(n.p:ℝ))-slack := by
    simp [Certificates.LayerNode.P,quadratic]
  have hK := had.control_K_bounds hc.1 hz huLow huHigh
  have hcoeff := had.control_coefficients_positive hc hz huLow huHigh
  have hdet := had.determinant_positive hc
  dsimp only [upperTrialData,Prod.fst,Prod.snd] at hK hcoeff hdet
  have hx0 : (0.28:ℝ)≤x := by
    have hh := hc.2.1.1
    norm_num [xLo] at hh
    linarith
  have hy0 : (0.28:ℝ)≤y := by
    have hh := (le_max_left xLo (n.p:ℝ)).trans hc.2.2.1
    norm_num [xLo] at hh
    linarith
  have hyp : (n.p:ℝ)≤y := (le_max_right xLo (n.p:ℝ)).trans hc.2.2.1
  have hU : 0≤z-(lam:ℝ) := by
    have hh := hz.1
    norm_num [zStart,lam] at hh ⊢
    linarith
  have hD : 0<Certificates.Control.det (2*(lam:ℝ)-x) (n.p+y-lam) n.R n.P := by
    rw [hR,hP]
    change (3/100:ℝ)<Certificates.Control.det (2*(lam:ℝ)-x) (n.p+y-lam)
      (primitive lam upperTrialData n.p) (quadratic lam (1-n.p)-slack) at hdet
    linarith
  have hcx : 0≤Certificates.Control.cx (z-lam) (n.p+y-lam) n.R
      (quadratic lam (z-n.p)-slack-u) := by
    rw [hR]
    have hh := hcoeff.1
    change (0.0145:ℝ)<Certificates.Control.cx (z-lam) (n.p+y-lam)
      (primitive lam upperTrialData n.p) (quadratic lam (z-n.p)-slack-u) at hh
    linarith only [hh]
  have hcy : 0≤Certificates.Control.cy (z-lam) (2*(lam:ℝ)-x) n.P
      (quadratic lam (z-n.p)-slack-u) := by
    rw [hP]
    have hh := hcoeff.2
    linarith
  have hb := Certificates.LayerNode.check_lower hn hU hK.1 hx0 hy0 hyp hD hcx hcy
  rw [hR,hP] at hb
  have he := controlH_eq_certified_value lam upperTrialData z u ((n.p:ℝ),x,y)
  rw [he]
  change _≤Certificates.Control.value (z-lam) (2*(lam:ℝ)-x) (n.p+y-lam)
    (primitive lam upperTrialData n.p) (quadratic lam (1-n.p)-slack)
    (quadratic lam (z-n.p)-slack-u) (UpperTrial.score x) (UpperTrial.score y)
  convert hb using 1 <;> (try simp only [upperTrialData]) <;> ring

end OptimalG.Variational
