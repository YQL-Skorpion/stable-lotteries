import OptimalG.LargeSelectedMassReduction
import OptimalG.LargeSelectedEnvelopeBounds
import OptimalG.LargePrimitiveIncrement
import OptimalG.DeficitQuadraticGrowth
import OptimalG.TailSelectedDeficit

namespace OptimalG
open Set Variational

/-- A deliberately coarse normalization bound on the selected strip. -/
theorem largeSelected_beta_upper {lam S p J : ℝ}
    (hL : (22493/40000:ℝ)≤lam) (hS : S≤11677/500000)
    (hp : p∈Icc (13/20:ℝ) (7/8))
    (hJ : quadratic lam p-S-J≤17/5000) : p/J≤19 := by
  have hLmul := mul_nonneg (sub_nonneg.mpr hL) (show 0≤p by linarith only [hp.1])
  have hquad := mul_nonneg (sub_nonneg.mpr hp.2)
    (show 0≤p+7/8-2*(22493/40000:ℝ) by linarith only [hp.1])
  have hJmin : 1/20<J := by
    unfold quadratic at hJ
    nlinarith only [hJ,hS,hLmul,hquad]
  rw [div_le_iff₀ (by linarith only [hJmin] : 0<J)]
  linarith only [hp.2,hJmin]

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- The explicit numerator and small-split scalar bound imply the actual
mixed inequality. In particular, the primitive cap is substituted only after
proving the necessary nonpositive sign of the K expression. -/
theorem largeSelected_of_numerator {S c p z q e Y H : ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (hp : p∈Icc (13/20:ℝ) (7/8)) (hz : z∈Icc (391/500:ℝ) (7/8)) (hpz : p≤z)
    (hq : q∈Icc (0:ℝ) lam)
    (hi : phi 0=Certificates.SmallMassExpressions.initial lam S)
    (hline : ∀ r∈Icc (9/25:ℝ) (391/500),phi r=lam-r)
    (hY : 8793/100000≤Y) (hH : -(3589/10000)≤H)
    (hfinish : curvePrimitive phi (7/8)=tailPrimitive (539/625) Y H (7/8))
    (he : e≤13/200) (hdef : e≤scoreDefect phi lam z)
    (hsmall : Certificates.SmallMassExpressions.primitive lam S (z-13/20)-quadratic lam z+S+
      (z-391/500)*e/2≤0)
    (hn : largeSelectedNumerator lam S z q e
      (largeRemainingLower lam S (Certificates.SmallMassExpressions.initial lam S)
        (Certificates.SmallMassExpressions.slope lam S) q)
      (largeRemainingUpper lam S (Certificates.SmallMassExpressions.initial lam S)
        (Certificates.SmallMassExpressions.slope lam S)) p≤0) :
    z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+phi z≤0 := by
  have hL : lam∈Icc (22493/40000:ℝ) (56233/100000) := by
    constructor <;> linarith only [g.lambda_mem.1,g.lambda_mem.2]
  have hp01 : p∈Ioo (0:ℝ) 1 := ⟨by linarith only [hp.1],by linarith only [hp.2]⟩
  have hz01 : z∈Icc (0:ℝ) 1 := ⟨by linarith only [hz.1],by linarith only [hz.2]⟩
  have hr : z-p+q∈Icc (0:ℝ) 1 :=
    ⟨by linarith only [hpz,hq.1],by linarith only [hz.2,hp.1,hq.2,hL.2]⟩
  have hanchor := g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩
  have hstart := h.primitive_eq_quadratic_on_line (by norm_num : (0:ℝ)≤9/25)
    (by norm_num : (9/25:ℝ)≤391/500) (by norm_num : (391/500:ℝ)≤1) hanchor hline
  have htriangle := h.primitiveDefect_le_triangle hc (by linarith only [hL.2]) hz.1
    (by linarith only [hz.2]) (hstart (391/500) ⟨by norm_num,le_rfl⟩)
    (hline (391/500) ⟨by norm_num,le_rfl⟩)
  have hJ := h.primitive_pos hp01
  have hcap := h.primitive_le_quadratic_after_anchor (a:=9/25) (by norm_num) hanchor p
    ⟨by linarith only [hp.1],by linarith only [hp.2]⟩
  have hR : 0<quadratic lam p-S := hJ.trans_le hcap
  have hd := h.selected_deficit_bound hL.2 hS.1 hY hH hanchor hfinish p
    ⟨by linarith only [hp.1],hp.2⟩
  have hbeta : p/curvePrimitive phi p≤19 := largeSelected_beta_upper hL.1 hS.2 hp hd.2
  have hcoef : (p/curvePrimitive phi p)*(z-391/500)/2≤1 := by
    have hm := mul_le_mul_of_nonneg_right hbeta (sub_nonneg.mpr hz.1)
    nlinarith only [hm,hz.2]
  let U := largeRemainingUpper lam S (Certificates.SmallMassExpressions.initial lam S)
    (Certificates.SmallMassExpressions.slope lam S) (z-p+q)
  let L := largeRemainingLower lam S (Certificates.SmallMassExpressions.initial lam S)
    (Certificates.SmallMassExpressions.slope lam S) q
  let K0 := quadratic lam (z-p+q)-quadratic lam z-quadratic lam q+S+U-L
  have hu := g.largeRemainingUpper_bound h hr
  have hl := g.largeRemainingLower_bound h hq
  rw [hi] at hu hl
  have hK : packingK phi p q z≤K0+(z-391/500)*(lam-z-phi z)/2 := by
    dsimp [K0,U,L]
    unfold packingK
    unfold binarySlackArea at hu hl
    unfold primitiveDefect scoreDefect at htriangle
    linarith only [hu,hl,htriangle]
  have hcheck : q-e+(p/(quadratic lam p-S))*(K0+(z-391/500)*e/2)≤0 := by
    apply mixed_deficit_check_of_numerator hR
    convert! hn using 1 <;> dsimp [U,L,largeSelectedNumerator] <;> unfold quadratic <;> ring
  have htop : K0+(z-391/500)*e/2≤0 := by
    by_cases hqsmall : q≤7/100
    · have hdelay : z-p∈Icc (0:ℝ) (9/40) := ⟨sub_nonneg.mpr hpz,by linarith only [hz.2,hp.1]⟩
      have hinc := largePrimitiveUpper_small_increment hL hS hdelay ⟨hq.1,hqsmall⟩
      have hb : z-13/20∈Icc (0:ℝ) (527/2000) :=
        ⟨by linarith only [hz.1],by linarith only [hz.2]⟩
      have hab : z-p≤z-13/20 := by linarith only [hp.1]
      have hf := h.positive ⟨hb.1,by linarith only [hz.2,hL.1]⟩
      rw [g.head (z-13/20) hb,hi] at hf
      have hm := mul_nonneg (sub_nonneg.mpr hab) hf.le
      have hs := smallMass_head_slope_nonpos hL hS
      have hext := mul_nonneg (neg_nonneg.mpr hs) (sq_nonneg ((z-13/20)-(z-p)))
      have hmono : Certificates.SmallMassExpressions.primitive lam S (z-p)≤
          Certificates.SmallMassExpressions.primitive lam S (z-13/20) := by
        unfold Certificates.SmallMassExpressions.primitive
        nlinarith only [hm,hext]
      have hhead : q≤527/2000 := by linarith only [hqsmall]
      have hid : K0+(z-391/500)*e/2=
          largePrimitiveUpper lam S (Certificates.SmallMassExpressions.initial lam S)
            (Certificates.SmallMassExpressions.slope lam S) (z-p+q)-
          Certificates.SmallMassExpressions.primitive lam S q-quadratic lam z+S+(z-391/500)*e/2 := by
        dsimp [K0,U,L,largePrimitiveUpper]
        rw [largeRemainingLower,if_pos hhead]
        unfold Certificates.SmallMassExpressions.primitive
        ring
      rw [hid]
      linarith only [hinc,hmono,hsmall]
    · exact normalized_mixed_K_nonpos (div_pos hp01.1 hR)
        (by linarith only [he,hqsmall]) hcheck
  exact mixed_residual_of_deficit_bounds hp01.1.le hJ hcap hK hcoef hdef htop hcheck

end VerifierCurve
end OptimalG
