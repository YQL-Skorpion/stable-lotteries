import OptimalG.CapHeadSlopeOrder
import OptimalG.IntermediateMixedCoverage
import OptimalG.IntermediateSelectedControl
import OptimalG.Certificates.StaticIntermediateSelectedLinks
import OptimalG.Certificates.StaticIntermediateTailLinks

/-! The actual intermediate-mass mixed test, after the finite selected and
tail certificates have been checked. No mixed inequality is assumed. -/
namespace OptimalG
open Set Variational
namespace VerifierCurve
variable {phi : ℝ→ℝ} (h : VerifierCurve phi (Certificates.StaticLow.lam:ℝ))
include h

theorem static_intermediate_mixed_verified {c p Y H : ℝ}
    (g : BinaryCurveGeometry phi (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) (Certificates.SmallMassExpressions.slope (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ)) c)
    (hS : (Certificates.StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hc : ConcaveOn ℝ (Icc (Certificates.StaticLow.lam:ℝ) 1) phi) (hp : p∈Icc (Certificates.StaticLow.lam:ℝ) (13/20:ℝ))
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ))
    (hline : ∀ r∈Icc (9/25:ℝ) (391/500),phi r=(Certificates.StaticLow.lam:ℝ)-r)

    (harea : binarySlackArea phi (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) (7/20)≤87/1000000000)
    (hcontrol : ∀ r∈Icc (391/500:ℝ) 1,phi r≤
      -Certificates.LineControl.theta (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ)*(r-(Certificates.StaticLow.lam:ℝ))-Certificates.LineControl.alpha (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ)*
        (quadratic (Certificates.StaticLow.lam:ℝ) (r-9/25)-(Certificates.StaticLow.slack:ℝ)-curvePrimitive phi r))
    (hY : 8793/100000≤Y) (hH : H∈Icc (-(3589/10000):ℝ) (-(1757/5000)))
    (hscore : ∀ z∈Icc (7/8:ℝ) 1,phi z=tailScore (539/625) Y H z)
    (hprimitive : ∀ z∈Icc (7/8:ℝ) 1,curvePrimitive phi z=tailPrimitive (539/625) Y H z) :
    ∀ q∈Icc (0:ℝ) (Certificates.StaticLow.lam:ℝ),∀ z∈Icc p 1,
      z+q-(Certificates.StaticLow.lam:ℝ)+(p/curvePrimitive phi p)*packingK phi p q z+
        intermediateEta phi (Certificates.StaticLow.lam:ℝ) (527/2000) p*phi z≤0 := by
  have hL : (Certificates.StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000) := by
    constructor <;> linarith only [g.lambda_mem.1,g.lambda_mem.2]
  have hcapOrder := capHeadSlopeOrder hL hS
  have hpbox : p∈Icc (22493/40000:ℝ) (13/20) := ⟨hL.1.trans hp.1,hp.2⟩
  have hD := Certificates.LineControl.denominator_pos hL hS
  have hN := Certificates.LineControl.slopeNumerator_pos hL hS
  have hm : 0<Certificates.LineControl.slope (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) := div_pos hN hD
  have hcap : ∀ r∈Icc (391/500:ℝ) 1,curvePrimitive phi r≤quadratic (Certificates.StaticLow.lam:ℝ) r-(Certificates.StaticLow.slack:ℝ) := by
    intro r hr
    exact h.primitive_le_quadratic_after_anchor (a:=9/25) (by norm_num)
      (g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩) r
      ⟨by linarith only [hr.1],hr.2⟩
  have hdef : ∀ z∈Icc (391/500:ℝ) (7/8),intermediateSelectedDeficit (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) z≤scoreDefect phi (Certificates.StaticLow.lam:ℝ) z := by
    intro z hz
    have hh := (h.lineControl_deficits hL hS hcap hcontrol).2 z
      ⟨hz.1,by linarith only [hz.2]⟩
    exact (cubicControlDeficit_le_clipped hm (Certificates.LineControl.alpha (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ))
      (Certificates.LineControl.crossing (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ)) z).trans hh
  exact h.intermediate_mixed_all_high g hS hc hp hinitial hline hcapOrder harea hdef
    (fun z hz=>Certificates.StaticIntermediateSelectedLinks.signs hL hS hpbox hz hD.ne' hN.ne')
    hY hH hscore hprimitive (Certificates.StaticIntermediateTailLinks.lo hL hS hpbox)
      (Certificates.StaticIntermediateTailLinks.hi hL hS hpbox)

end VerifierCurve
end OptimalG
