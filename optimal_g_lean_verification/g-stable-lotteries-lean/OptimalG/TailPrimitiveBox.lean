import OptimalG.HighMassGeometry
import OptimalG.TailAnchorOrder

/-! Four endpoint tests suffice for the direct tail inequality when the mass
primitive lies in an interval. This keeps its correlation with the score
coefficient, and uses only the lower anchor height. -/
namespace OptimalG
open Set

noncomputable def directTailPrimitiveEnvelope
    (a lam p z q upper lower mass Y H : ℝ) : ℝ :=
  mass*(z+q-lam+tailScore a Y H z)+p*(upper-tailPrimitive a Y H z-lower)

private theorem affine_nonpos_of_interval {C D lo hi x : ℝ}
    (hx : x∈Icc lo hi) (hl : lo*D+C≤0) (hh : hi*D+C≤0) : x*D+C≤0 := by
  by_cases hD : 0≤D
  · have hm := mul_le_mul_of_nonneg_right hx.2 hD
    linarith only [hm,hh]
  · have hm := mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hD)
    linarith only [hm,hl]

theorem directTailPrimitiveEnvelope_nonpos {a lam p z q upper lower mass lo hi Ylo Y Hlo Hhi H : ℝ}
    (ha : a<1) (hz : z∈Icc a 1) (hp : 0≤p) (hm : 0≤mass)
    (hbox : mass∈Icc lo hi) (hY : Ylo≤Y) (hH : H∈Icc Hlo Hhi)
    (hll : directTailPrimitiveEnvelope a lam p z q upper lower lo Ylo Hlo≤0)
    (hlh : directTailPrimitiveEnvelope a lam p z q upper lower lo Ylo Hhi≤0)
    (hhl : directTailPrimitiveEnvelope a lam p z q upper lower hi Ylo Hlo≤0)
    (hhh : directTailPrimitiveEnvelope a lam p z q upper lower hi Ylo Hhi≤0) :
    directTailPrimitiveEnvelope a lam p z q upper lower mass Y H≤0 := by
  have hleft : directTailPrimitiveEnvelope a lam p z q upper lower mass Ylo Hlo≤0 :=
    affine_nonpos_of_interval hbox hll hhl
  have hright : directTailPrimitiveEnvelope a lam p z q upper lower mass Ylo Hhi≤0 :=
    affine_nonpos_of_interval hbox hlh hhh
  let C := mass*(z+q-lam)+p*(upper-lower)
  have hl : C+mass*tailScore a Ylo Hlo z-p*tailPrimitive a Ylo Hlo z≤0 := by
    convert! hleft using 1 <;> dsimp [C,directTailPrimitiveEnvelope] <;> ring
  have hh : C+mass*tailScore a Ylo Hhi z-p*tailPrimitive a Ylo Hhi z≤0 := by
    convert! hright using 1 <;> dsimp [C,directTailPrimitiveEnvelope] <;> ring
  have hactual := weighted_tail_nonpos_of_anchor_endpoints ha hz hY hH hp hm hl hh
  convert! hactual using 1 <;> dsimp [C,directTailPrimitiveEnvelope] <;> ring

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- The supplied four scalar residuals bound the actual curve, including its
actual normalization p/J(p), by proved primitive comparisons. -/
theorem mixed_tail_of_primitive_box {a p q z upper lower lo hi Ylo Y Hlo Hhi H : ℝ}
    (ha : a<1) (hp : p∈Ioo (0:ℝ) 1) (hz : z∈Icc a 1)
    (hscore : phi z=tailScore a Y H z)
    (hprimitive : curvePrimitive phi z=tailPrimitive a Y H z)
    (hupper : curvePrimitive phi (z-p+q)≤upper)
    (hlower : lower≤curvePrimitive phi q)
    (hbox : curvePrimitive phi p∈Icc lo hi) (hY : Ylo≤Y) (hH : H∈Icc Hlo Hhi)
    (hll : directTailPrimitiveEnvelope a lam p z q upper lower lo Ylo Hlo≤0)
    (hlh : directTailPrimitiveEnvelope a lam p z q upper lower lo Ylo Hhi≤0)
    (hhl : directTailPrimitiveEnvelope a lam p z q upper lower hi Ylo Hlo≤0)
    (hhh : directTailPrimitiveEnvelope a lam p z q upper lower hi Ylo Hhi≤0) :
    z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+phi z≤0 := by
  have hJ := h.primitive_pos hp
  have he := directTailPrimitiveEnvelope_nonpos ha hz hp.1.le hJ.le hbox hY hH hll hlh hhl hhh
  have hK : packingK phi p q z≤upper-tailPrimitive a Y H z-lower := by
    unfold packingK
    rw [hprimitive]
    linarith only [hupper,hlower]
  have hm := mul_le_mul_of_nonneg_left hK hp.1.le
  have hn : curvePrimitive phi p*(z+q-lam+phi z)+p*packingK phi p q z≤0 := by
    rw [hscore]
    dsimp only [directTailPrimitiveEnvelope] at he
    linarith only [he,hm]
  have hid : curvePrimitive phi p*(z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+phi z)=
      curvePrimitive phi p*(z+q-lam+phi z)+p*packingK phi p q z := by
    field_simp [hJ.ne']
    ring
  apply nonpos_of_mul_nonpos_left (b:=curvePrimitive phi p) _ hJ
  rw [mul_comm,hid]
  exact hn

end VerifierCurve
end OptimalG
