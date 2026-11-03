import OptimalG.ClippedCorrection
import OptimalG.Certificates.FarClippedAlgebra

/-! A truncated affine head gives a sharp integral bound for every far split.
It uses only monotonicity beyond the head, not a sampled score profile. -/
namespace OptimalG
open Set MeasureTheory

private theorem integral_head_line (F s q h : ℝ) :
    (∫ u in (0:ℝ)..h,F+s*q+s*u)=h*(F+s*q)+s*h^2/2 := by
  let P := fun u : ℝ => (F+s*q)*u+s*u^2/2
  have hd (u : ℝ) : HasDerivAt P (F+s*q+s*u) u := by
    convert! ((hasDerivAt_id u).const_mul (F+s*q)).add
      ((((hasDerivAt_id u).pow 2).const_mul s).div_const 2) using 1 <;>
      first | rfl | (simp only [id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((by fun_prop : Continuous (fun u : ℝ => F+s*q+s*u)).intervalIntegrable 0 h)]
  dsimp [P]
  ring

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (hc : VerifierCurve phi lam)
include hc

theorem head_increment_upper {F slope xh q h : ℝ}
    (hxh : xh∈Icc (0:ℝ) 1)
    (hhead : ∀ r∈Icc (0:ℝ) xh,phi r=F+slope*r)
    (hq : q∈Icc (0:ℝ) xh) (hh : 0≤h) (hqh : q+h≤1) :
    curvePrimitive phi (q+h)-curvePrimitive phi q≤
      h*(F+slope*q)+slope*h^2/2-slope*(max (q+h-xh) 0)^2/2 := by
  have hpoint (u : ℝ) (hu : u∈Icc (0:ℝ) h) :
      phi (q+u)≤F+slope*q+slope*u-slope*max (u-(xh-q)) 0 := by
    have hqu : q+u∈Icc (0:ℝ) 1 := ⟨by linarith only [hq.1,hu.1],by linarith only [hu.2,hqh]⟩
    by_cases hr : q+u≤xh
    · rw [hhead (q+u) ⟨hqu.1,hr⟩,max_eq_right (by linarith only [hr])]
      nlinarith
    · have hm := hc.decreasing.antitoneOn hxh hqu (le_of_not_ge hr)
      rw [hhead xh ⟨hxh.1,le_rfl⟩] at hm
      rw [max_eq_left (by linarith only [hr])]
      nlinarith only [hm]
  have hi : IntervalIntegrable (fun u : ℝ => F+slope*q+slope*u) volume 0 h :=
    (by fun_prop : Continuous (fun u : ℝ => F+slope*q+slope*u)).intervalIntegrable 0 h
  have hm : IntervalIntegrable (fun u : ℝ => max (u-(xh-q)) 0) volume 0 h :=
    (by fun_prop : Continuous (fun u : ℝ => max (u-(xh-q)) 0)).intervalIntegrable 0 h
  have hhbound := intervalIntegral.integral_mono_on hh
    (hc.shift_integrable hq.1 hh hqh) (hi.sub (hm.const_mul slope)) hpoint
  rw [hc.shift_integral hq.1 hh hqh,
    intervalIntegral.integral_sub hi (hm.const_mul slope),
    integral_head_line,intervalIntegral.integral_const_mul,
    integral_positive_ramp (sub_nonneg.mpr hq.2) hh] at hhbound
  have he : h-(xh-q)=q+h-xh := by ring
  rw [he] at hhbound
  nlinarith only [hhbound]

theorem farClipped_average_nonneg {p q x : ℝ}
    (hp : p<1) (hq : 0≤q) (hqx : q+(1-p)≤x) (hx : x≤1) :
    0≤packingDelta phi p q/(1-p)-phi x := by
  have hh : 0<1-p := sub_pos.mpr hp
  have hi := hc.primitive_increment_lower hq
    (show q≤q+(1-p) by linarith only [hh]) (hqx.trans hx)
  have hm := hc.decreasing.antitoneOn
    (show q+(1-p)∈Icc (0:ℝ) 1 by constructor <;> linarith only [hq,hh,hqx,hx])
    (show x∈Icc (0:ℝ) 1 by constructor <;> linarith only [hq,hh,hqx,hx]) hqx
  have hs := mul_le_mul_of_nonneg_left hm hh.le
  have hb : phi x≤packingDelta phi p q/(1-p) := by
    apply (le_div_iff₀ hh).mpr
    unfold packingDelta
    have he : 1-p+q=q+(1-p) := by ring
    rw [he]
    nlinarith only [hi,hs]
  linarith only [hb]

end VerifierCurve
end OptimalG
