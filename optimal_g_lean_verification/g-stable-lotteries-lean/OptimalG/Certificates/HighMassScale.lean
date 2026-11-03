import OptimalG.Certificates.LineControlBounds
import OptimalG.Certificates.HighMassData.ScaleCentral
import OptimalG.Certificates.HighMassData.ScaleTail
import OptimalG.TailReanchor

namespace OptimalG.Certificates
open Set

theorem highMass_scale_central {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (17/20)) :
    (129/100)*(Variational.quadratic lam p-S)<p*(1-p) := by
  have hn := HighMassData.ScaleCentral.numerator_pos hL hS hp
  have hd := HighMassData.ScaleCentral.denominator_pos hL hS hp
  have he : p*(1-p)-(129/100)*(Variational.quadratic lam p-S)=
      HighMassData.ScaleCentral.numerator lam S p/HighMassData.ScaleCentral.denominator lam S p := by
    norm_num [HighMassData.ScaleCentral.numerator,HighMassData.ScaleCentral.denominator,Variational.quadratic]
    <;> ring
  have hh := div_pos hn hd
  rw [←he] at hh
  linarith only [hh]

theorem highMass_scale_tail {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (7/8:ℝ) (22/25)) :
    (129/100)*tailPrimitive (539/625) (221/2500) (-(1757/5000)) p<p*(1-p) := by
  have hn := HighMassData.ScaleTail.numerator_pos hL hS hp
  have hd := HighMassData.ScaleTail.denominator_pos hL hS hp
  have he : p*(1-p)-(129/100)*tailPrimitive (539/625) (221/2500) (-(1757/5000)) p=
      HighMassData.ScaleTail.numerator lam S p/HighMassData.ScaleTail.denominator lam S p := by
    rw [tailPrimitive_anchor_linear (by norm_num : (539/625:ℝ)≠1)]
    norm_num [HighMassData.ScaleTail.numerator,HighMassData.ScaleTail.denominator]
    <;> ring
  have hh := div_pos hn hd
  rw [←he] at hh
  linarith only [hh]

end Certificates

namespace VerifierCurve
open Set
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- Three small polynomial bounds prove the normalized scale condition.
The middle bound uses the exact fixed line control; the last uses the
same terminal polynomial expressed at the fixed anchor. -/
theorem highMass_large_scale {S Ya Ha : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hcap : ∀ p∈Icc (13/20:ℝ) (17/20),curvePrimitive phi p≤Variational.quadratic lam p-S)
    (hdeficit : ∀ p∈Icc (17/20:ℝ) (7/8),
      curvePrimitive phi p≤Variational.quadratic lam p-S-
        Certificates.LineControl.slope lam S*(p-Certificates.LineControl.crossing lam S)^2/2)
    (hY : Ya≤221/2500) (hH : Ha≤-(1757/5000))
    (htail : ∀ p∈Icc (7/8:ℝ) (22/25),
      curvePrimitive phi p=tailPrimitive (539/625) Ya Ha p) :
    ∀ p∈Icc (13/20:ℝ) (22/25),129/100≤(p/curvePrimitive phi p)*(1-p) := by
  intro p hp
  have hJ := h.primitive_pos (q:=p) ⟨by linarith only [hp.1],by linarith only [hp.2]⟩
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hJ).mpr
  by_cases h85 : p≤17/20
  · have hn := Certificates.highMass_scale_central hL hS ⟨hp.1,h85⟩
    have hm := mul_le_mul_of_nonneg_left (hcap p ⟨hp.1,h85⟩) (by norm_num : (0:ℝ)≤129/100)
    linarith only [hn,hm]
  · by_cases h875 : p≤7/8
    · have hn := Certificates.LineControl.scaleExact_pos hL hS ⟨le_of_not_ge h85,h875⟩
      have hm := mul_le_mul_of_nonneg_left (hdeficit p ⟨le_of_not_ge h85,h875⟩)
        (by norm_num : (0:ℝ)≤129/100)
      linarith only [hn,hm]
    · have hpp : p∈Icc (7/8:ℝ) (22/25) := ⟨le_of_not_ge h875,hp.2⟩
      have hn := Certificates.highMass_scale_tail hL hS hpp
      have ht := tailPrimitive_mono_anchor (by norm_num : (539/625:ℝ)<1)
        (show p∈Icc (539/625:ℝ) 1 by constructor <;> linarith only [hpp.1,hpp.2]) hY hH
      have hm := mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ)≤129/100)
      rw [htail p hpp]
      linarith only [hn,hm]

end VerifierCurve
end OptimalG
