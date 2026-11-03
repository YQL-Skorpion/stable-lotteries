import OptimalG.LargeMixedCoverage
import OptimalG.Certificates.StaticLargeSelectedBounds
import OptimalG.Certificates.StaticLargeTailCornerSigns
import OptimalG.LineControlDeficit
import OptimalG.CapHeadSlopeOrder

/-! Assembly intended for checking after the finite selected/tail data.
Every scalar sign and the cap/head order is supplied internally. -/
namespace OptimalG
open Set Variational
namespace VerifierCurve
variable {phi : ℝ→ℝ} (h : VerifierCurve phi (Certificates.StaticLow.lam:ℝ))
include h

theorem static_large_mixed_verified {c p Y H : ℝ}
    (g : BinaryCurveGeometry phi (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) (Certificates.SmallMassExpressions.slope (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ)) c)
    (hS : (Certificates.StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hconc : ConcaveOn ℝ (Icc (Certificates.StaticLow.lam:ℝ) 1) phi)
    (hp : p∈Icc (13/20:ℝ) (37/40))
    (hY : Y∈Icc (8793/100000:ℝ) (221/2500))
    (hH : H∈Icc (-3589/10000:ℝ) (-1757/5000))
    (hline : ∀ r∈Icc (9/25:ℝ) (391/500),phi r=(Certificates.StaticLow.lam:ℝ)-r)
    (htail : ∀ r∈Icc (7/8:ℝ) 1,phi r=tailScore (539/625) Y H r)
    (hprimitive : ∀ r∈Icc (7/8:ℝ) 1,curvePrimitive phi r=tailPrimitive (539/625) Y H r)
    (hv : tailBackwardSlope (539/625) Y H≤321/50)
    (hg : (1077/100:ℝ)≤tailBackwardCurvature (539/625) Y H)
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ))
    (harea : binarySlackArea phi (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) (7/20)≤87/1000000000)
    (hscore : scoreDefect phi (Certificates.StaticLow.lam:ℝ) (7/20)≤3/12500)
    (hbinary : ∀ q∈Icc (0:ℝ) (Certificates.StaticLow.lam:ℝ),q+(p/curvePrimitive phi p)*packingDelta phi p q≤(Certificates.StaticLow.lam:ℝ))
    (hcontrol : ∀ r∈Icc (391/500:ℝ) 1,phi r≤
      -Certificates.LineControl.theta (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ)*(r-(Certificates.StaticLow.lam:ℝ))-Certificates.LineControl.alpha (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ)*
        (quadratic (Certificates.StaticLow.lam:ℝ) (r-9/25)-(Certificates.StaticLow.slack:ℝ)-curvePrimitive phi r)) :
    ∀ q∈Icc (0:ℝ) (Certificates.StaticLow.lam:ℝ),∀ z∈Icc p 1,
      z+q-(Certificates.StaticLow.lam:ℝ)+(p/curvePrimitive phi p)*packingK phi p q z+phi z≤0 := by
  have hL : (Certificates.StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000) := by
    constructor <;> linarith only [g.lambda_mem.1,g.lambda_mem.2]
  have hm : 0<Certificates.LineControl.slope (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) := div_pos
    (Certificates.LineControl.slopeNumerator_pos hL hS) (Certificates.LineControl.denominator_pos hL hS)
  have hcap : ∀ r∈Icc (391/500:ℝ) 1,curvePrimitive phi r≤quadratic (Certificates.StaticLow.lam:ℝ) r-(Certificates.StaticLow.slack:ℝ) := by
    intro r hr
    exact h.primitive_le_quadratic_after_anchor (a:=9/25) (by norm_num)
      (g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩) r
      ⟨by linarith only [hr.1],hr.2⟩
  have hdef : ∀ z∈Icc (391/500:ℝ) (7/8),Certificates.LargeSelectedExpressions.cubic (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) z≤scoreDefect phi (Certificates.StaticLow.lam:ℝ) z := by
    intro z hz
    have hh := (h.lineControl_deficits hL hS hcap hcontrol).2 z
      ⟨hz.1,by linarith only [hz.2]⟩
    exact (cubicControlDeficit_le_clipped hm (Certificates.LineControl.alpha (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ))
      (Certificates.LineControl.crossing (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ)) z).trans hh
  exact h.large_mixed_all_high_of_signs g hS hconc hp hY hH hline htail hprimitive
    hv hg hinitial (capHeadSlopeOrder hL hS) harea hscore hbinary
    (fun z hz hp82=>Certificates.staticLargeTail_corner_signs hL hS ⟨hp.1,hp82⟩ hz)
    (Certificates.staticLargeSelected_signs hL hS) hm.le hdef

end VerifierCurve
end OptimalG
