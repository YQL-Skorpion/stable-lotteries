import OptimalG.HighMassGeometry
import OptimalG.PolynomialCompletion

/-! A terminal mixed test follows from its binary endpoint whenever a small
polynomial certificate makes the entire terminal residual nondecreasing. -/
namespace OptimalG
open Set
namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem mixed_tail_of_derivative_numerator {p q R a Y H : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hp : p∈Icc (41/50:ℝ) (37/40)) (hq : q∈Icc (0:ℝ) lam)
    (ha : a≠1)
    (hline : ∀ r∈Icc (9/25:ℝ) (391/500),phi r=lam-r)
    (htail : ∀ z∈Icc (7/8:ℝ) 1,phi z=tailScore a Y H z)
    (hcap : curvePrimitive phi p≤R)
    (hnum : ∀ z∈Icc (7/8:ℝ) 1,
      0≤R*(1+tailSlope a Y H z)+p*(p-z-tailScore a Y H z))
    (hbinary : q+(p/curvePrimitive phi p)*packingDelta phi p q≤lam)
    {z : ℝ} (hz : z∈Icc (7/8:ℝ) 1) (hpz : p≤z) :
    z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+phi z≤0 := by
  have hp0 : 0<p := by linarith only [hp.1]
  have hp1 : p<1 := by linarith only [hp.2]
  have hJp : 0<curvePrimitive phi p := h.primitive_pos ⟨hp0,hp1⟩
  have hR : 0<R := hJp.trans_le hcap
  have hb : 0≤p/curvePrimitive phi p := (div_pos hp0 hJp).le
  have hbet : p/R≤p/curvePrimitive phi p := div_le_div_of_nonneg_left hp0.le hJp hcap
  let start : ℝ := max p (7/8)
  let G : ℝ→ℝ := fun t=>t+q-lam+(p/curvePrimitive phi p)*packingK phi p q t+tailScore a Y H t
  have hstart : start≤1 := max_le hp1.le (by norm_num)
  have hstartp : p≤start := le_max_left _ _
  have hstartt : (7/8:ℝ)≤start := le_max_right _ _
  have hcomp : ContinuousOn (fun t=>curvePrimitive phi (t-p+q)) (Icc start 1) := by
    apply h.primitive_continuous.comp ((continuous_id.sub continuous_const).add continuous_const).continuousOn
    intro t ht
    change 0≤t-p+q ∧ t-p+q≤1
    constructor <;> linarith only [ht.1,ht.2,hstartp,hq.1,hq.2,hL.2,hp.1]
  have hJ : ContinuousOn (curvePrimitive phi) (Icc start 1) :=
    h.primitive_continuous.mono (Icc_subset_Icc (hp0.le.trans hstartp) le_rfl)
  have hT : ContinuousOn (tailScore a Y H) (Icc start 1) :=
    (tailScore_continuous a Y H).continuousOn
  have hcont : ContinuousOn G (Icc start 1) := by
    dsimp [G,packingK]
    fun_prop
  have hder (t : ℝ) (ht : t∈interior (Icc start 1)) :
      HasDerivAt G (1+(p/curvePrimitive phi p)*(phi (t-p+q)-phi t)+tailSlope a Y H t) t := by
    rw [interior_Icc] at ht
    have ht' : t∈Ioo (0:ℝ) 1 := ⟨hp0.trans_le (hstartp.trans ht.1.le),ht.2⟩
    have hr : t-p+q∈Ioo (0:ℝ) 1 := by
      constructor <;> linarith only [ht.1,ht.2,hstartp,hq.1,hq.2,hL.2,hp.1]
    have hs := (h.primitive_hasDerivAt hr).comp t (((hasDerivAt_id t).sub_const p).add_const q)
    have hj := h.primitive_hasDerivAt ht'
    have hd := ((((hasDerivAt_id t).add_const q).sub_const lam).add
      (((hs.sub hj).sub_const (curvePrimitive phi q)).const_mul (p/curvePrimitive phi p))).add
      (tailScore_hasDerivAt a Y H t)
    convert! hd using 1 <;> first | rfl | (simp only [id_eq,mul_one] <;> ring)
  have hmono : MonotoneOn G (Icc start 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc start 1) hcont
      (fun t ht=>(hder t ht).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hder t ht).deriv]
    rw [interior_Icc] at ht
    have htT : t∈Icc (7/8:ℝ) 1 := ⟨hstartt.trans ht.1.le,ht.2.le⟩
    have htP : p≤t := hstartp.trans ht.1.le
    have hm : t-p+lam∈Icc (9/25:ℝ) (391/500) := by
      constructor <;> linarith only [htP,ht.2,hp.1,hL.1,hL.2]
    have hml : t-p+lam∈Icc (0:ℝ) 1 := ⟨by linarith only [hm.1],by linarith only [hm.2]⟩
    have hrl : t-p+q∈Icc (0:ℝ) 1 := by
      constructor <;> linarith only [htP,ht.2,hq.1,hq.2,hL.2,hp.1]
    have hdelay := h.decreasing.antitoneOn hrl hml (by linarith only [hq.2])
    rw [hline _ hm] at hdelay
    have hdelay' : p-t≤phi (t-p+q) := by linarith only [hdelay]
    have htphi := htail t htT
    have hceil := h.ceiling t ⟨by linarith only [htT.1],htT.2⟩
    have hc : 0≤p-t-tailScore a Y H t := by rw [←htphi];linarith only [hceil,hp.1,hL.2]
    have hm1 := mul_le_mul_of_nonneg_left hdelay' hb
    have hm2 := mul_le_mul_of_nonneg_right hbet hc
    have hn := hnum t htT
    have he : R*(1+(p/R)*(p-t-tailScore a Y H t)+tailSlope a Y H t)=
        R*(1+tailSlope a Y H t)+p*(p-t-tailScore a Y H t) := by
      field_simp [hR.ne']
      ring
    have hn' : 0≤1+(p/R)*(p-t-tailScore a Y H t)+tailSlope a Y H t :=
      nonneg_of_mul_nonneg_right (he.symm ▸ hn) hR
    rw [htphi]
    nlinarith only [hm1,hm2,hn']
  have hz' : z∈Icc start 1 := ⟨max_le hpz hz.1,hz.2⟩
  have hlast := hmono hz' (right_mem_Icc.mpr hstart) hz.2
  have hend : G 1≤0 := by
    have he : G 1=q-lam+(p/curvePrimitive phi p)*packingDelta phi p q := by
      dsimp [G,packingK,packingDelta]
      rw [tailScore_at_one a Y H ha,show curvePrimitive phi 1=0 from h.integral_zero]
      ring
    rw [he]
    linarith only [hbinary]
  have hh := hlast.trans hend
  simpa only [G,←htail z hz] using hh

end VerifierCurve
end OptimalG
