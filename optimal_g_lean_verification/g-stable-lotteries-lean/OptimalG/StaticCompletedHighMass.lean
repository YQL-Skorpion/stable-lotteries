import OptimalG.HighMassAssembly
import OptimalG.CompletedCurveFacts
import OptimalG.HighMassFarClipped
import OptimalG.Certificates.HighMassBasic
import OptimalG.Certificates.HighMassLowRatio
import OptimalG.Certificates.HighMassScale
import OptimalG.StaticIntermediateMassMixedVerified
import OptimalG.StaticLargeMassMixedVerified

/-! Assemble every high-mass test for the actual completed curve. All bounded
mixed, ratio and scale inequalities come from their finite certificate wrappers.
The binary theorem and completed-curve geometry remain explicit inputs. -/
namespace OptimalG
open Set Variational

namespace VerifierCurve
variable {phi : ℝ → ℝ} (h : VerifierCurve phi (Certificates.StaticLow.lam:ℝ))
include h

theorem static_completed_curve_high_mass {c Y H : ℝ}
    (g : BinaryCurveGeometry phi (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) (Certificates.SmallMassExpressions.slope (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ)) c)
    (hS : (Certificates.StaticLow.slack:ℝ) ∈ Icc (227179/10000000 : ℝ) (11677/500000))
    (hconc : ConcaveOn ℝ (Icc (Certificates.StaticLow.lam:ℝ) 1) phi)
    (hline : ∀ r ∈ Icc (9/25 : ℝ) (391/500), phi r=(Certificates.StaticLow.lam:ℝ)-r)
    (harea : binarySlackArea phi (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) (7/20) ≤ 87/1000000000)
    (hscore : scoreDefect phi (Certificates.StaticLow.lam:ℝ) (7/20) ≤ 3/12500)
    (hY : Y ∈ Icc (8793/100000 : ℝ) (221/2500))
    (hH : H ∈ Icc (-3589/10000 : ℝ) (-1757/5000))
    (hv : tailBackwardSlope (539/625) Y H ∈ Icc (309/50 : ℝ) (321/50))
    (hk : tailBackwardCurvature (539/625) Y H ∈ Icc (1077/100 : ℝ) (1273/100))
    (htail : ∀ r ∈ Icc (7/8 : ℝ) 1, phi r=tailScore (539/625) Y H r)
    (hprimitive : ∀ r ∈ Icc (7/8 : ℝ) 1,
      curvePrimitive phi r=tailPrimitive (539/625) Y H r)
    (hbinary : ∀ p ∈ Ioo (Certificates.StaticLow.lam:ℝ) 1, ∀ q ∈ Icc (0 : ℝ) (Certificates.StaticLow.lam:ℝ),
      q+(p/curvePrimitive phi p)*packingDelta phi p q ≤ (Certificates.StaticLow.lam:ℝ))
    (hcontrol : ∀ r ∈ Icc (391/500 : ℝ) 1, phi r ≤
      -Certificates.LineControl.theta (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ)*(r-(Certificates.StaticLow.lam:ℝ))-Certificates.LineControl.alpha (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ)*
        (quadratic (Certificates.StaticLow.lam:ℝ) (r-9/25)-(Certificates.StaticLow.slack:ℝ)-curvePrimitive phi r)) :
    VerifierOn (Ioo (Certificates.StaticLow.lam:ℝ) 1) phi (Certificates.StaticLow.lam:ℝ) (fun p => p/curvePrimitive phi p)
      (highMassCorrection phi (Certificates.StaticLow.lam:ℝ)) := by
  have hinitial := g.initial_eq
  have hL : (Certificates.StaticLow.lam:ℝ) ∈ Icc (22493/40000 : ℝ) (56233/100000) :=
    ⟨by linarith only [g.lambda_mem.1],by linarith only [g.lambda_mem.2]⟩
  have hfall := g.fall_through_line (top:=391/500)
    (fun r hr => hline r ⟨by linarith only [hr.1,hL.1],hr.2⟩)
  have hupper := h.primitive_le_quadratic_after_anchor
    (a:=9/25) (by constructor <;> norm_num)
    (g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩)
  have hdef := (h.lineControl_deficits hL hS
    (fun r hr => hupper r ⟨by linarith only [hr.1],hr.2⟩) hcontrol).1
  have hcone : ∀ r ∈ Icc (22/25 : ℝ) 1,
      -1+2*(1-r) ≤ phi r ∧ phi r ≤ -1+(67/10)*(1-r) := by
    intro r hr
    rw [htail r ⟨by linarith only [hr.1],hr.2⟩]
    exact polynomial_tail_cones (by norm_num : (539/625 : ℝ) ≠ 1)
      (by linarith only [hk.1]) (by linarith only [hv.2])
      (by linarith only [hv.1,hk.2]) r hr
  have hbasic (p : ℝ) (hp : p ∈ Ioc (Certificates.StaticLow.lam:ℝ) (13/20 : ℝ)) :=
    Certificates.HighMassBasic.intermediate_bounds h hL hS hp
      (g.line_primitive p ⟨by linarith only [hp.1,hL.1],by linarith only [hp.2]⟩)
      (by
        have hh := h.primitive_relative_quadratic_antitone
          (a:=1-p) (b:=31/40)
          ⟨by linarith only [hp.2],by linarith only [hp.1,hL.1]⟩
          (by constructor <;> norm_num) (by linarith only [hp.1,hL.1])
        dsimp only at hh
        rw [g.line_primitive (31/40) ⟨by norm_num,le_rfl⟩] at hh
        linarith only [hh]) hinitial
      (g.cap_score (527/2000) ⟨le_rfl,by linarith only [g.contact_mem.1]⟩)
  have hmid (p : ℝ) (hp : p ∈ Ioc (Certificates.StaticLow.lam:ℝ) (13/20 : ℝ)) :=
    h.static_intermediate_mixed_verified g hS hconc ⟨hp.1.le,hp.2⟩ hinitial hline
      harea hcontrol hY.1 (by constructor <;> linarith only [hH.1,hH.2]) htail hprimitive
  have hlarge (p : ℝ) (hp : p ∈ Icc (13/20 : ℝ) (37/40)) :=
    h.static_large_mixed_verified g hS hconc hp hY hH hline htail hprimitive hv.2 hk.1
      hinitial harea hscore
      (hbinary p ⟨by linarith only [hp.1,hL.2],by linarith only [hp.2]⟩) hcontrol
  have hn : HighMassIntervalBounds phi (Certificates.StaticLow.lam:ℝ) (527/2000) := by
    refine ⟨fun p hp => (hbasic p hp).1,
      fun p hp => (hbasic p hp).2.1,
      fun p hp => (hbasic p hp).2.2.2,?_,?_,?_,?_,?_,?_,?_⟩
    · intro p hp q hq z hz
      exact hmid p hp q hq z ⟨by linarith only [hp.2,hz.1],by linarith only [hz.2]⟩
    · intro p hp q hq z hz
      exact hmid p hp q hq z ⟨by linarith only [hp.2,hz.1],hz.2⟩
    · exact Certificates.highMass_low_ratio h hL hS
        (fun r hr => by rw [g.head r hr,hinitial]; rfl)
        (fun r hr => hline r ⟨hr.1,by linarith only [hr.2,hL.2]⟩)
        (fun a b ha hab hb => hfall a b ha hab (by linarith only [hb]))
    · exact h.highMass_large_scale hL hS
        (fun p hp => hupper p ⟨by linarith only [hp.1],by linarith only [hp.2]⟩)
        hdef hY.2 (by linarith only [hH.2])
        (fun p hp => hprimitive p ⟨hp.1,by linarith only [hp.2]⟩)
    · intro p hp x hx q hq hxq
      exact h.highMass_far_clipped g.head (by linarith only [g.head_slope])
        (fun a b ha hab hb => hfall a b ha hab (by linarith only [hb]))
        hcone hp hx hq hxq
    · intro p hp q hq z hz
      exact hlarge p hp q hq z ⟨hz.1,by linarith only [hz.2]⟩
    · intro p hp q hq z hz hpz
      exact hlarge p hp q hq z ⟨hpz,hz.2⟩
  exact h.highMass_verifier
    ⟨by linarith only [hL.1],by linarith only [hL.2]⟩
    ⟨by norm_num,by linarith only [hL.1]⟩ hconc g.head
    (fun r hr => hline r ⟨hr.1,by linarith only [hr.2]⟩)
    (fun a b ha hab hb => hfall a b ha hab (by linarith only [hb]))
    hcone hbinary hn

end VerifierCurve
end OptimalG
