import OptimalG.FarClippedHeadIntegral

/-! The entire C5 far-clipped condition follows from the affine head,
the lower slope bound, and the endpoint tail cone. -/
namespace OptimalG
open Set

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (hc : VerifierCurve phi lam)
include hc

theorem far_clipped_of_head {F slope p q x t : ℝ}
    (hp : p∈Ico (22/25:ℝ) 1)
    (hq : q∈Icc (0:ℝ) (9/50)) (hx : x∈Icc (9/50:ℝ) (9/25))
    (hv : 9/50≤x-q)
    (hhead : ∀ r∈Icc (0:ℝ) (527/2000),phi r=F+slope*r)
    (hslope : -(691/1000:ℝ)≤slope)
    (hfall : ∀ a b,0≤a→a≤b→b≤9/25→a-b≤phi b-phi a)
    (ht : t∈Icc (0:ℝ) ((1-(1-p))/(1-67*(1-p)/20))) :
    q-x+t*(packingDelta phi p q/(1-p)-phi x)≤0 := by
  let width := 1-p
  let A := packingDelta phi p q/width-phi x
  let tmax := (1-width)/(1-67*width/20)
  have hw : width∈Ioc (0:ℝ) (3/25) := by
    dsimp [width]
    constructor <;> linarith only [hp.1,hp.2]
  have hden : 0<1-67*width/20 := by linarith only [hw.2]
  have htmax : 0≤tmax := div_nonneg (by linarith only [hw.2]) hden.le
  have hA0 : 0≤A := hc.farClipped_average_nonneg hp.2 hq.1
    (by change q+width≤x; linarith only [hv,hw.2]) (by linarith only [hx.2])
  have hi := hc.head_increment_upper
    (show (527/2000:ℝ)∈Icc 0 1 by constructor <;> norm_num) hhead
    (show q∈Icc (0:ℝ) (527/2000) by constructor <;> linarith only [hq.1,hq.2])
    hw.1.le (show q+width≤1 by linarith only [hq.2,hw.2])
  have hDelta : packingDelta phi p q≤
      width*(F+slope*q)+slope*width^2/2-slope*(max (q+width-527/2000) 0)^2/2 := by
    unfold packingDelta
    rw [show 1-p+q=q+width by dsimp [width]; ring]
    exact hi
  have hscale : t*A≤tmax*A := mul_le_mul_of_nonneg_right ht.2 hA0
  by_cases hxh : x≤527/2000
  · have hov : max (q+width-527/2000) 0=0 :=
      max_eq_right (by linarith only [hv,hw.2,hxh])
    rw [hov] at hDelta
    norm_num at hDelta
    have hxhead := hhead x ⟨by linarith only [hx.1],hxh⟩
    have haverage : packingDelta phi p q/width≤phi x-slope*(x-q-width/2) := by
      apply (div_le_iff₀ hw.1).mpr
      rw [hxhead]
      nlinarith only [hDelta]
    have hs := mul_le_mul_of_nonneg_right
      (show -slope≤(691/1000:ℝ) by linarith only [hslope])
      (show 0≤x-q-width/2 by linarith only [hv,hw.2])
    have hA : A≤(691/1000)*(x-q-width/2) := by
      dsimp [A]
      nlinarith only [haverage,hs]
    have htop := mul_le_mul_of_nonneg_left hA htmax
    have hbound := Certificates.farClipped_head_bound ⟨hw.1.le,hw.2⟩
      (show x-q∈Icc (9/50:ℝ) (527/2000) by constructor <;> linarith only [hv,hq.1,hxh])
    change tmax*((691/1000)*(x-q-width/2))≤x-q at hbound
    change q-x+t*A≤0
    linarith only [hscale,htop,hbound]
  · let d := (527/2000:ℝ)-q
    let e := max (q+width-527/2000) 0
    let B := d-width/2+e^2/(2*width)
    have hB : 0≤B := by
      have hh := div_nonneg (sq_nonneg e) (by linarith only [hw.1] : 0≤2*width)
      dsimp [B,d]
      linarith only [hh,hq.2,hw.2]
    have hprod : B*width=d*width-width^2/2+e^2/2 := by
      dsimp [B]
      field_simp [hw.1.ne'] <;> ring
    have hphi := hfall (527/2000) x (by norm_num) (le_of_not_ge hxh) hx.2
    rw [hhead (527/2000) ⟨by norm_num,le_rfl⟩] at hphi
    have hphiscale := mul_le_mul_of_nonneg_right hphi hw.1.le
    have haverage : packingDelta phi p q/width≤phi x+(x-q)-d-slope*B := by
      apply (div_le_iff₀ hw.1).mpr
      have hprod' := congrArg (fun v : ℝ => slope*v) hprod
      change packingDelta phi p q≤width*(F+slope*q)+slope*width^2/2-slope*e^2/2 at hDelta
      dsimp [d] at hprod' ⊢
      nlinarith only [hDelta,hphiscale,hprod']
    have hs := mul_le_mul_of_nonneg_right
      (show -slope≤(691/1000:ℝ) by linarith only [hslope]) hB
    have he : Certificates.farClippedEnvelope width q x=(x-q)-d+(691/1000)*B := by
      dsimp [Certificates.farClippedEnvelope,B,d,e]
      field_simp [hw.1.ne']
      ring
    have hA : A≤Certificates.farClippedEnvelope width q x := by
      rw [he]
      dsimp [A]
      nlinarith only [haverage,hs]
    have htop := mul_le_mul_of_nonneg_left hA htmax
    have hbound := Certificates.farClipped_free_bound hw hq hx.2
    change tmax*Certificates.farClippedEnvelope width q x≤x-q at hbound
    change q-x+t*A≤0
    linarith only [hscale,htop,hbound]

end VerifierCurve
end OptimalG
