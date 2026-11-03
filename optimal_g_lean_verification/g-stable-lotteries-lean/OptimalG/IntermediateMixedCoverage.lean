import OptimalG.IntermediateSelectedAssembly
import OptimalG.IntermediateTailAssembly

/-! The selected and terminal scalar tests cover every high rank for
intermediate masses. The omitted straight portion is filled by convexity,
and the needed coefficient and slope properties are derived here. -/
namespace OptimalG
open Set Variational
open Certificates.IntermediateTailExpressions (etaNumerator complementUpper)

namespace BinaryCurveGeometry

theorem fall_through_line {phi : ℝ→ℝ} {lam S slope c top : ℝ}
    (g : BinaryCurveGeometry phi lam S slope c)
    (hline : ∀ r∈Icc lam top,phi r=lam-r) :
    ∀ a b,0≤a→a≤b→b≤top→a-b≤phi b-phi a := by
  intro a b ha hab hb
  by_cases hbl : b≤lam
  · exact g.low_slope a b ha hab hbl
  · have hLb := le_of_not_ge hbl
    rw [hline b ⟨hLb,hb⟩]
    by_cases hal : a≤lam
    · have hh := g.low_slope a lam ha hal le_rfl
      rw [hline lam ⟨le_rfl,hLb.trans hb⟩] at hh
      linarith only [hh]
    · rw [hline a ⟨le_of_not_ge hal,hab.trans hb⟩]
      ring_nf
      rfl

end BinaryCurveGeometry
namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem intermediate_eta_pos_of_area {S c p : ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc lam (13/20:ℝ))
    (harea : binarySlackArea phi lam S (7/20)≤87/1000000000) :
    0 < intermediateEta phi lam (527/2000) p := by
  have hL : lam∈Icc (22493/40000:ℝ) (56233/100000) := by
    constructor <;> linarith only [g.lambda_mem.1,g.lambda_mem.2]
  have hp01 : p∈Ioo (0:ℝ) 1 := ⟨by linarith only [hp.1,hL.1],by linarith only [hp.2]⟩
  have hJ := h.primitive_pos hp01
  have hFactual : phi (527/2000)=Certificates.IntermediateTailExpressions.headScore lam S :=
    g.cap_score (527/2000) ⟨le_rfl,by linarith only [g.contact_mem.1]⟩
  have hsign := intermediate_tail_coefficient_signs hL hS hp
  have hF : 0<phi (527/2000) := hFactual.symm ▸ hsign.1
  have hR := g.line_primitive p ⟨by linarith only [hp.1,hL.1],by linarith only [hp.2]⟩
  have hP : curvePrimitive phi (1-p)≤complementUpper lam S p :=
    h.intermediate_complement_primitive_upper ⟨hp01.1.le,hp.2⟩ harea
  have hid : intermediateEta phi lam (527/2000) p*(curvePrimitive phi p*phi (527/2000))=
      etaNumerator lam S p+p*(complementUpper lam S p-curvePrimitive phi (1-p)) := by
    unfold intermediateEta intermediateCorrection
    field_simp [hJ.ne',hF.ne']
    rw [hR,hFactual]
    unfold etaNumerator Certificates.IntermediateTailExpressions.massFactor
      Certificates.IntermediateTailExpressions.massPrimitive
    ring
  have hh := mul_nonneg hp01.1.le (sub_nonneg.mpr hP)
  have hpos : 0 < intermediateEta phi lam (527/2000) p*(curvePrimitive phi p*phi (527/2000)) := by
    rw [hid]
    linarith only [hsign.2,hh]
  exact pos_of_mul_pos_left hpos (mul_nonneg hJ.le hF.le)

/-- Explicit selected-strip and terminal-tail scalar signs give the actual
mixed inequality for every high rank from p to one. -/
theorem intermediate_mixed_all_high {S c p Y H : ℝ} {deficit : ℝ→ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hc : ConcaveOn ℝ (Icc lam 1) phi) (hp : p∈Icc lam (13/20:ℝ))
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial lam S)
    (hline : ∀ r∈Icc (9/25:ℝ) (391/500),phi r=lam-r)
    (hcapOrder : ∀ u∈Icc (0:ℝ) (9/25),∀ v∈Icc (0:ℝ) (9/25),u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤capScore lam S v-capScore lam S u)
    (harea : binarySlackArea phi lam S (7/20)≤87/1000000000)
    (hdef : ∀ z∈Icc (391/500:ℝ) (7/8),deficit z≤scoreDefect phi lam z)
    (hselected : ∀ z∈Icc (391/500:ℝ) (7/8),IntermediateSelectedSigns lam S p z (deficit z))
    (hY : 8793/100000≤Y) (hH : H∈Icc (-(3589/10000):ℝ) (-(1757/5000)))
    (hscore : ∀ z∈Icc (7/8:ℝ) 1,phi z=tailScore (539/625) Y H z)
    (hprimitive : ∀ z∈Icc (7/8:ℝ) 1,curvePrimitive phi z=tailPrimitive (539/625) Y H z)
    (hntailLo : IntermediateTailPolynomialSigns lam S p (-(3589/10000)))
    (hntailHi : IntermediateTailPolynomialSigns lam S p (-(1757/5000))) :
    ∀ q∈Icc (0:ℝ) lam,∀ z∈Icc p 1,
      z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+
        intermediateEta phi lam (527/2000) p*phi z≤0 := by
  have hL : lam∈Icc (22493/40000:ℝ) (56233/100000) := by
    constructor <;> linarith only [g.lambda_mem.1,g.lambda_mem.2]
  have hsign := intermediate_tail_coefficient_signs hL hS hp
  have hline' : ∀ r∈Icc lam (391/500:ℝ),phi r=lam-r := by
    intro r hr
    exact hline r ⟨by linarith only [hr.1,hL.1],hr.2⟩
  have hstart := h.primitive_eq_quadratic_on_line (by norm_num : (0:ℝ)≤9/25)
    (by norm_num : (9/25:ℝ)≤391/500) (by norm_num : (391/500:ℝ)≤1)
    (g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩) hline
    (391/500) ⟨by norm_num,le_rfl⟩
  have hzero := hline (391/500) ⟨by norm_num,le_rfl⟩
  have hhigh (q : ℝ) (hq : q∈Icc (0:ℝ) lam) (z : ℝ) (hz : z∈Icc (391/500:ℝ) 1) :
      z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+
        intermediateEta phi lam (527/2000) p*phi z≤0 := by
    by_cases hzt : z≤7/8
    · exact h.intermediate_selected_of_signs g hS hc hp ⟨hz.1,hzt⟩ hinitial hstart hzero
        hcapOrder harea (hdef z ⟨hz.1,hzt⟩) (hselected z ⟨hz.1,hzt⟩) q hq
    · have hz' : z∈Icc (7/8:ℝ) 1 := ⟨le_of_not_ge hzt,hz.2⟩
      exact h.intermediate_tail_of_polynomial_signs g hp hz' hinitial hsign.1 hsign.2.le
        hcapOrder harea hY hH (hscore z hz') (hprimitive z hz') hntailLo hntailHi q hq
  have hp01 : p∈Ioo (0:ℝ) 1 := ⟨by linarith only [hp.1,hL.1],by linarith only [hp.2]⟩
  have hJ := h.primitive_pos hp01
  intro q hq z hz
  by_cases hzt : z≤391/500
  · exact h.highMass_middle_of_endpoint hp.1 hq (by linarith only [hp.2])
      (by norm_num) (div_nonneg hp01.1.le hJ.le) (h.intermediate_eta_pos_of_area g hS hp harea).le
      (div_mul_cancel₀ p hJ.ne') hline' (g.fall_through_line hline')
      (hhigh q hq (391/500) ⟨le_rfl,by norm_num⟩) z ⟨hz.1,hzt⟩
  · exact hhigh q hq z ⟨le_of_not_ge hzt,hz.2⟩

end VerifierCurve
end OptimalG
