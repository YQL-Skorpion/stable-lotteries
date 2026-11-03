import OptimalG.LargeTailBeforeAssembly
import OptimalG.LargeTailHighAssembly
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.LargeTailMassBounds
import OptimalG.HighMassNearEndpoint
import OptimalG.HighMassTailMonotone

/-! Assembly of the direct tail tests with the actual mass normalization.
The remaining finite inputs are explicit corner signs, never assumptions
of the mixed inequality itself. -/
namespace OptimalG
open Set Variational Certificates.LargeTailExpressions

structure LargeTailCornerSigns (lam S p z : ℝ) : Prop where
  before : z≤97/100 → ∀ M, (M=largeTailMassFloor lam S p ∨ M=massCap lam S p) →
    ∀ H, (H= -3589/10000 ∨ H= -1757/5000) →
      LargeTailSplitSigns lam S p M z (8793/100000) H
  high : ∀ M, (M=largeTailMassFloor lam S p ∨ M=massCap lam S p) →
    ∀ H, (H= -3589/10000 ∨ H= -1757/5000) →
      LargeTailHighSigns lam S p M z (8793/100000) H
  late : 97/100≤z → ∀ M, (M=largeTailMassFloor lam S p ∨ M=massCap lam S p) →
    ∀ H, (H= -3589/10000 ∨ H= -1757/5000) →
      LargeTailLateHeadSigns lam S p M z (8793/100000) H

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem largeTail_mixed_of_corner_signs {S c p z Y H : ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hconc : ConcaveOn ℝ (Icc lam 1) phi)
    (hp : p∈Icc (13/20:ℝ) (41/50)) (hz : z∈Icc (7/8:ℝ) 1)
    (hY : 8793/100000≤Y) (hH : H∈Icc (-3589/10000:ℝ) (-1757/5000))
    (hline : ∀ r∈Icc (9/25:ℝ) (391/500),phi r=lam-r)
    (htail : ∀ r∈Icc (7/8:ℝ) 1,phi r=tailScore (539/625) Y H r)
    (hprimitive : ∀ r∈Icc (7/8:ℝ) 1,curvePrimitive phi r=tailPrimitive (539/625) Y H r)
    (hv : tailBackwardSlope (539/625) Y H≤321/50)
    (hg : (1077/100:ℝ)≤tailBackwardCurvature (539/625) Y H)
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial lam S)
    (hcapOrder : ∀ u∈Icc (0:ℝ) (9/25),∀ v∈Icc (0:ℝ) (9/25),u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤capScore lam S v-capScore lam S u)
    (harea : binarySlackArea phi lam S (7/20)≤87/1000000000)
    (hscore : scoreDefect phi lam (7/20)≤3/12500)
    (hbinary : ∀ q∈Icc (0:ℝ) lam,q+(p/curvePrimitive phi p)*packingDelta phi p q≤lam)
    (hn : LargeTailCornerSigns lam S p z) :
    ∀ q∈Icc (0:ℝ) lam,z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+phi z≤0 := by
  have hL : lam∈Icc (22493/40000:ℝ) (56233/100000) := by
    constructor <;> linarith only [g.lambda_mem.1,g.lambda_mem.2]
  have hbox := h.largeTail_mass_box hconc hL.2 hS.1 hY (by linarith only [hH.1]) hline
    (g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩)
    (hprimitive (7/8) ⟨le_rfl,by norm_num⟩) hp
  have hscalar := g.largeTail_scalar_inputs h hS
  have hp01 : p∈Ioo (0:ℝ) 1 := ⟨by linarith only [hp.1],by linarith only [hp.2]⟩
  intro q hq
  by_cases hnear : 97/100≤z ∧ q≤1/20
  · exact h.highMass_small_split_near_endpoint hL hS.1
      ⟨hp.1,by linarith only [hp.2]⟩ ⟨hq.1,hnear.2⟩ (by norm_num) hv hg
      (hline (2/5) ⟨by norm_num,by norm_num⟩) htail hbox.2 (hbinary q hq) ⟨hnear.1,hz.2⟩
  have corner (M : ℝ) (hM : M=largeTailMassFloor lam S p ∨ M=massCap lam S p)
      (HH : ℝ) (hHH : HH= -3589/10000 ∨ HH= -1757/5000) :
      core lam p M z (8793/100000) HH q
        (curvePrimitive phi (z-p+q)) (curvePrimitive phi q)≤0 := by
    by_cases hb : z≤97/100
    · exact g.fixed_large_tail_before_nonpos h hp ⟨hz.1,hb⟩ hinitial
        hscalar.1 hscalar.2.1 hscalar.2.2.1 hscalar.2.2.2 hcapOrder
        (hn.before hb M hM HH hHH) q hq
    · have hz97 : 97/100≤z := le_of_not_ge hb
      by_cases hqh : 527/2000≤q
      · exact g.fixed_large_tail_high_nonpos h hp hz ⟨hqh,hq.2⟩
          hscalar.2.1 hscalar.2.2.1 hscalar.2.2.2 (hn.high M hM HH hHH)
      · have hq05 : 1/20≤q := by
          by_contra hq05
          exact hnear ⟨hz97,le_of_not_ge hq05⟩
        exact g.fixed_large_tail_late_head_nonpos h hp ⟨hz97,hz.2⟩ ⟨hq05,le_of_not_ge hqh⟩
          hinitial harea hscore (hn.late hz97 M hM HH hHH)
  exact h.mixed_tail_of_primitive_box (by norm_num) hp01
    ⟨by linarith only [hz.1],hz.2⟩ (htail z hz) (hprimitive z hz) le_rfl le_rfl hbox hY hH
    (corner _ (Or.inl rfl) _ (Or.inl rfl)) (corner _ (Or.inl rfl) _ (Or.inr rfl))
    (corner _ (Or.inr rfl) _ (Or.inl rfl)) (corner _ (Or.inr rfl) _ (Or.inr rfl))

/-- All large masses on the terminal strip: the upper mass range propagates
from the actual binary endpoint and the lower range uses the finite corners. -/
theorem highMass_tail_of_corner_signs {S c p z Y H : ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hconc : ConcaveOn ℝ (Icc lam 1) phi)
    (hp : p∈Icc (13/20:ℝ) (37/40)) (hz : z∈Icc (7/8:ℝ) 1) (hpz : p≤z)
    (hY : Y∈Icc (8793/100000:ℝ) (221/2500))
    (hH : H∈Icc (-3589/10000:ℝ) (-1757/5000))
    (hline : ∀ r∈Icc (9/25:ℝ) (391/500),phi r=lam-r)
    (htail : ∀ r∈Icc (7/8:ℝ) 1,phi r=tailScore (539/625) Y H r)
    (hprimitive : ∀ r∈Icc (7/8:ℝ) 1,curvePrimitive phi r=tailPrimitive (539/625) Y H r)
    (hv : tailBackwardSlope (539/625) Y H≤321/50)
    (hg : (1077/100:ℝ)≤tailBackwardCurvature (539/625) Y H)
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial lam S)
    (hcapOrder : ∀ u∈Icc (0:ℝ) (9/25),∀ v∈Icc (0:ℝ) (9/25),u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤capScore lam S v-capScore lam S u)
    (harea : binarySlackArea phi lam S (7/20)≤87/1000000000)
    (hscore : scoreDefect phi lam (7/20)≤3/12500)
    (hbinary : ∀ q∈Icc (0:ℝ) lam,q+(p/curvePrimitive phi p)*packingDelta phi p q≤lam)
    (hn : p≤41/50→LargeTailCornerSigns lam S p z) :
    ∀ q∈Icc (0:ℝ) lam,z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+phi z≤0 := by
  by_cases hpl : p≤41/50
  · exact h.largeTail_mixed_of_corner_signs g hS hconc ⟨hp.1,hpl⟩ hz hY.1 hH
      hline htail hprimitive hv hg hinitial hcapOrder harea hscore hbinary (hn hpl)
  · have hL : lam∈Icc (22493/40000:ℝ) (56233/100000) := by
      constructor <;> linarith only [g.lambda_mem.1,g.lambda_mem.2]
    have hcap := h.primitive_le_quadratic_after_anchor (a:=9/25) (by norm_num)
      (g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩) p
      ⟨by linarith only [hp.1],by linarith only [hp.2]⟩
    intro q hq
    exact h.highMass_tail_monotone hL hS.1 ⟨le_of_not_ge hpl,hp.2⟩ hq hY hH
      hline htail hcap (hbinary q hq) hz hpz

end VerifierCurve
end OptimalG
