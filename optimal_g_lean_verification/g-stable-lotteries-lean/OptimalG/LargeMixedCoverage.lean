import OptimalG.LargeTailVerification
import OptimalG.LargeSelectedAssembly
import OptimalG.IntermediateMixedCoverage

/-! The selected and terminal reductions cover every high rank for large
masses. The straight interval below .782 follows from its actual endpoint. -/
namespace OptimalG
open Set Variational
namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem large_mixed_all_high_of_signs {S c p Y H : ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hconc : ConcaveOn ℝ (Icc lam 1) phi)
    (hp : p∈Icc (13/20:ℝ) (37/40))
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
    (hntail : ∀ z∈Icc (7/8:ℝ) 1,p≤41/50→LargeTailCornerSigns lam S p z)
    (hnselected : LargeSelectedSigns lam S)
    (hm : 0≤Certificates.LineControl.slope lam S)
    (hdef : ∀ z∈Icc (391/500:ℝ) (7/8),Certificates.LargeSelectedExpressions.cubic lam S z≤scoreDefect phi lam z) :
    ∀ q∈Icc (0:ℝ) lam,∀ z∈Icc p 1,
      z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+phi z≤0 := by
  have hL : lam∈Icc (22493/40000:ℝ) (56233/100000) := by
    constructor <;> linarith only [g.lambda_mem.1,g.lambda_mem.2]
  have hline' : ∀ r∈Icc lam (391/500:ℝ),phi r=lam-r := by
    intro r hr
    exact hline r ⟨by linarith only [hr.1,hL.1],hr.2⟩
  have hhigh (q : ℝ) (hq : q∈Icc (0:ℝ) lam) (z : ℝ)
      (hz : z∈Icc (391/500:ℝ) 1) (hpz : p≤z) :
      z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+phi z≤0 := by
    by_cases hzt : z≤7/8
    · exact h.largeSelected_of_signs g hS hconc ⟨hp.1,hpz.trans hzt⟩ ⟨hz.1,hzt⟩ hpz hq
        hinitial hline hcapOrder hY.1 (by linarith only [hH.1])
        (hprimitive (7/8) ⟨le_rfl,by norm_num⟩) hm (hdef z ⟨hz.1,hzt⟩) hnselected
    · have hz' : z∈Icc (7/8:ℝ) 1 := ⟨le_of_not_ge hzt,hz.2⟩
      exact h.highMass_tail_of_corner_signs g hS hconc hp hz' hpz hY hH hline htail hprimitive
        hv hg hinitial hcapOrder harea hscore hbinary (hntail z hz') q hq
  have hp01 : p∈Ioo (0:ℝ) 1 := ⟨by linarith only [hp.1],by linarith only [hp.2]⟩
  have hJ := h.primitive_pos hp01
  intro q hq z hz
  by_cases hzt : z≤391/500
  · have hps : p≤391/500 := hz.1.trans hzt
    have hh := h.highMass_middle_of_endpoint
      (by linarith only [hp.1,hL.2] : lam≤p) hq hps (by norm_num : (391/500:ℝ)≤1)
      (div_nonneg hp01.1.le hJ.le) (by norm_num : (0:ℝ)≤1)
      (div_mul_cancel₀ p hJ.ne') hline' (g.fall_through_line hline')
      (by simpa only [one_mul] using hhigh q hq (391/500) ⟨le_rfl,by norm_num⟩ hps)
      z ⟨hz.1,hzt⟩
    simpa only [one_mul] using hh
  · exact hhigh q hq z ⟨le_of_not_ge hzt,hz.2⟩ hz.1

end VerifierCurve
end OptimalG
