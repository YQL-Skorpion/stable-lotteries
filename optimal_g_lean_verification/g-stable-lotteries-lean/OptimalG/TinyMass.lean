import OptimalG.SmallMassSupport
import OptimalG.HighMassGeometry

/-! The entire mass interval (0, .04] is verified from the completed curve's
head bounds and tail cone. No interval-arithmetic certificate depends on p. -/
namespace OptimalG
open Set

noncomputable def tinyMassBeta (phi : ℝ→ℝ) (lam p : ℝ) : ℝ :=
  (lam+p)/(curvePrimitive phi p+curvePrimitive phi (1-p))

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem tinyMass_test {p slope : ℝ}
    (hp : p∈Ioc (0:ℝ) (1/25))
    (hlam : lam∈Icc (22493/40000:ℝ) (562329/1000000))
    (hphi0 : phi 0∈Icc (109/250:ℝ) (443/1000))
    (hlow : ∀ u∈Icc 0 lam,phi 0-u≤phi u)
    (hhead : ∀ u∈Icc (0:ℝ) (527/2000),phi u=phi 0+slope*u)
    (hjoin : phi (527/2000)≤13/50)
    (htail : ∀ u∈Icc (24/25:ℝ) 1,
      -1+2*(1-u)≤phi u ∧ phi u≤-1+(67/10)*(1-u)) :
    ThreeFunctionTest phi lam p (tinyMassBeta phi lam p) (1+tinyMassBeta phi lam p*p) := by
  let R := curvePrimitive phi p
  let P := curvePrimitive phi (1-p)
  let beta := tinyMassBeta phi lam p
  have hp1 : p<1 := by linarith only [hp.2]
  have hpl : p≤lam := by linarith only [hp.2,hlam.1]
  have hRpos : 0<R := h.primitive_pos ⟨hp.1,hp1⟩
  have hPpos : 0<P := h.primitive_pos ⟨by linarith only [hp1],by linarith only [hp.1]⟩
  have hD : 0<R+P := add_pos hRpos hPpos
  have hb : 0≤beta := (div_pos (by linarith only [hlam.1,hp.1]) hD).le
  have heq : beta*(R+P)=lam+p := div_mul_cancel₀ _ (ne_of_gt hD)
  have hRlower : (39/100)*p≤R := by
    have ha := h.primitive_above_tangent ⟨hp.1.le,hp1.le⟩
    have hs := hlow p ⟨hp.1.le,hpl⟩
    have hs' : (39/100:ℝ)≤phi p := by linarith only [hs,hphi0.1,hp.2]
    have hm := mul_le_mul_of_nonneg_left hs' hp.1.le
    dsimp [R]
    nlinarith only [ha,hm]
  have hRupper : R≤(443/1000)*p := by
    have ha := h.primitive_increment_upper (a:=0) le_rfl hp.1.le hp1.le
    have hm := mul_le_mul_of_nonneg_left hphi0.2 hp.1.le
    simp only [curvePrimitive,intervalIntegral.integral_same,sub_zero] at ha
    dsimp [R,curvePrimitive]
    nlinarith only [ha,hm]
  have hPupper : P≤p := by
    have hh := h.primitive_le_tail (q:=1-p) ⟨by linarith only [hp1],by linarith only [hp.1]⟩
    dsimp [P]
    linarith only [hh]
  have hPlower : (21/25)*p≤P := by
    have hh := h.primitive_tail_cones (p:=1-p)
      ⟨by linarith only [hp1],by linarith only [hp.1]⟩ (fun u hu =>
        htail u ⟨by linarith only [hu.1,hp.2],hu.2⟩)
    have hpp := mul_le_mul_of_nonneg_left hp.2 hp.1.le
    dsimp [P]
    nlinarith only [hh.1,hpp,hp.1]
  have hbp0 : 0≤beta*p := mul_nonneg hb hp.1.le
  have hbp : beta*p≤49/100 := by
    have hm := mul_le_mul_of_nonneg_left (show (123/100)*p≤R+P by
      linarith only [hRlower,hPlower]) hb
    nlinarith only [hm,heq,hlam.2,hp.2]
  have hmargin : (1289/10000:ℝ)≤beta*R-p := by
    have hm := mul_le_mul_of_nonneg_left (show (39/100)*P≤R by
      linarith only [hPupper,hRlower]) hb
    nlinarith only [hm,heq,hlam.1,hp.2]
  have hb2 : 2≤beta := by
    change 2≤(lam+p)/(R+P)
    apply (le_div_iff₀ hD).mpr
    nlinarith only [hRupper,hPupper,hp.2,hlam.1]
  have hgap : 1≤beta*(phi 0-lam+1-p) := by
    have hh : (1/2:ℝ)≤phi 0-lam+1-p := by
      linarith only [hphi0.1,hlam.2,hp.2]
    have hm := mul_le_mul_of_nonneg_left hh hb
    nlinarith only [hm,hb2]
  have hhead0 : (1+beta*p)*phi 0≤lam+(beta*p)*(13/50) := by
    have hm := mul_le_mul_of_nonneg_left hphi0.2 (by linarith only [hbp0] : 0≤1+beta*p)
    nlinarith only [hm,hlam.1,hbp]
  have hsupport := h.head_support_of_ceiling
    (show (527/2000:ℝ)∈Icc 0 lam by constructor <;> linarith only [hlam.1])
    hbp0 hhead hjoin hhead0
  have htarget : lam+(beta*p)*(13/50)≤lam-p+beta*R := by
    nlinarith only [hmargin,hbp]
  have hidentity : lam-p+beta*R=2*lam-beta*P := by
    nlinarith only [heq]
  apply h.tinyMass_threeFunctionTest hp.1 hpl hb hlow hgap
    (target:=lam-p+beta*R)
  · exact hidentity.le
  · rfl
  · intro x hx
    exact (hsupport x hx).trans htarget

end VerifierCurve
end OptimalG
