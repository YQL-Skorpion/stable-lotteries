import OptimalG.HighMassGeometry
import OptimalG.TailAnchorOrder
import OptimalG.ExtendedSlackProfiles

/-! The intermediate correction can be bounded using one genuine remaining
area estimate. Its contribution keeps the sign of the negative high score. -/
namespace OptimalG
open Set Variational
namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem intermediate_complement_primitive_upper {S eps p : ℝ}
    (hp : p∈Icc (0:ℝ) (13/20))
    (harea : binarySlackArea phi lam S (7/20)≤eps) :
    curvePrimitive phi (1-p)≤quadratic lam (1-p)-S+eps := by
  have hr : 1-p∈Icc (0:ℝ) 1 := by constructor <;> linarith only [hp.1,hp.2]
  have hm := h.binarySlackArea_antitone S
    (show (7/20:ℝ)∈Icc 0 1 by constructor <;> norm_num) hr
    (by linarith only [hp.2])
  unfold binarySlackArea at hm harea
  linarith only [hm,harea]

/-- Clearing the two positive denominators gives a direct primitive test.
The complementary-primitive upper bound is used only against a nonpositive
score, preserving the direction of the intermediate correction. -/
theorem intermediate_mixed_of_primitive_bounds {p q z xh upper lower Pup : ℝ}
    (hp : p∈Ioo (0:ℝ) 1) (hF : 0<phi xh) (hzscore : phi z≤0)
    (hP : curvePrimitive phi (1-p)≤Pup)
    (hupper : curvePrimitive phi (z-p+q)≤upper)
    (hlower : lower≤curvePrimitive phi q)
    (hcheck : curvePrimitive phi p*phi xh*(z+q-lam)+
      (curvePrimitive phi p*phi xh+lam*curvePrimitive phi p-p*Pup)*phi z+
      p*phi xh*(upper-curvePrimitive phi z-lower)≤0) :
    z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+
      intermediateEta phi lam xh p*phi z≤0 := by
  have hJ := h.primitive_pos hp
  have hK : packingK phi p q z≤upper-curvePrimitive phi z-lower := by
    unfold packingK
    linarith only [hupper,hlower]
  have hmK := mul_le_mul_of_nonneg_left hK (mul_nonneg hp.1.le hF.le)
  have hmD := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg hp.1.le (sub_nonneg.mpr hP)) hzscore
  have hid : (z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+
      intermediateEta phi lam xh p*phi z)*(curvePrimitive phi p*phi xh)=
      curvePrimitive phi p*phi xh*(z+q-lam)+
      (curvePrimitive phi p*phi xh+lam*curvePrimitive phi p-
        p*curvePrimitive phi (1-p))*phi z+p*phi xh*packingK phi p q z := by
    unfold intermediateEta intermediateCorrection
    field_simp [hJ.ne',hF.ne']
    ring
  apply nonpos_of_mul_nonpos_left (b:=curvePrimitive phi p*phi xh) _ (mul_pos hJ hF)
  rw [hid]
  nlinarith only [hcheck,hmK,hmD]

/-- The upper-tail correction requires only the two anchor-score endpoints
at the lower anchor height once the primitive bounds are established. -/
theorem intermediate_tail_of_primitive_bounds {a p q z xh upper lower Pup Ylo Y Hlo Hhi H : ℝ}
    (ha : a<1) (hp : p∈Ioo (0:ℝ) 1) (hz : z∈Icc a 1)
    (hF : 0<phi xh) (hzscore : phi z≤0)
    (hP : curvePrimitive phi (1-p)≤Pup)
    (hupper : curvePrimitive phi (z-p+q)≤upper)
    (hlower : lower≤curvePrimitive phi q)
    (hY : Ylo≤Y) (hH : H∈Icc Hlo Hhi)
    (hscore : phi z=tailScore a Y H z)
    (hprimitive : curvePrimitive phi z=tailPrimitive a Y H z)
    (hD : 0≤curvePrimitive phi p*phi xh+lam*curvePrimitive phi p-p*Pup)
    (hlo : curvePrimitive phi p*phi xh*(z+q-lam)+
      (curvePrimitive phi p*phi xh+lam*curvePrimitive phi p-p*Pup)*tailScore a Ylo Hlo z+
      p*phi xh*(upper-tailPrimitive a Ylo Hlo z-lower)≤0)
    (hhi : curvePrimitive phi p*phi xh*(z+q-lam)+
      (curvePrimitive phi p*phi xh+lam*curvePrimitive phi p-p*Pup)*tailScore a Ylo Hhi z+
      p*phi xh*(upper-tailPrimitive a Ylo Hhi z-lower)≤0) :
    z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+
      intermediateEta phi lam xh p*phi z≤0 := by
  apply h.intermediate_mixed_of_primitive_bounds hp hF hzscore hP hupper hlower
  let C := curvePrimitive phi p*phi xh*(z+q-lam)+p*phi xh*(upper-lower)
  let D := curvePrimitive phi p*phi xh+lam*curvePrimitive phi p-p*Pup
  have hl : C+D*tailScore a Ylo Hlo z-(p*phi xh)*tailPrimitive a Ylo Hlo z≤0 := by
    convert! hlo using 1 <;> dsimp [C,D] <;> ring
  have hh : C+D*tailScore a Ylo Hhi z-(p*phi xh)*tailPrimitive a Ylo Hhi z≤0 := by
    convert! hhi using 1 <;> dsimp [C,D] <;> ring
  have ht := weighted_tail_nonpos_of_anchor_endpoints ha hz hY hH
    (mul_nonneg hp.1.le hF.le) hD hl hh
  rw [hscore,hprimitive]
  convert! ht using 1 <;> dsimp [C,D] <;> ring

end VerifierCurve
end OptimalG
