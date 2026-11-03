import OptimalG.IntermediateSmallMass
import OptimalG.SmallMassDefectControl
import OptimalG.VerifierPrimitiveCap

/-! The intermediate small-mass test applied to a line-anchored completed
curve and one genuine fixed differential control. -/
namespace OptimalG
open Set

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem intermediateSmallMass_test_of_control {S p slope pc theta alpha : ℝ}
    (hlam : lam∈Icc (1/2:ℝ) (57/100)) (hS : S∈Icc (0:ℝ) (3/100))
    (hp : p∈Icc (1/25:ℝ) (7/50)) (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (hhead : ∀ x∈Icc (0:ℝ) (527/2000),phi x=phi 0+slope*x)
    (hcap : ∀ x∈Icc (527/2000:ℝ) (7/25),phi x=Variational.capScore lam S x)
    (hline : ∀ z∈Icc (19/50:ℝ) (391/500),phi z=lam-z)
    (hfall : ∀ a b,0≤a→a≤b→b≤391/500→a-b≤phi b-phi a)
    (hanchor : curvePrimitive phi (19/50)=Variational.quadratic lam (19/50)-S)
    (halpha : 0≤alpha) (hslope : (13/50:ℝ)≤theta-1+alpha*pc)
    (hcross : 0≤(theta-1+alpha*pc)*(789/1000-lam)-alpha*pc^2/2)
    (hcontrol : ∀ z∈Icc (391/500:ℝ) 1,phi z≤
      -theta*(z-lam)-alpha*(Variational.quadratic lam (z-pc)-S-curvePrimitive phi z))
    (hn : IntermediateSmallMassChecks phi lam S p) :
    ThreeFunctionTest phi lam p (smallMassBeta (curvePrimitive phi) lam S p)
      (intermediateSmallEta phi lam S p) := by
  have hprimitive := h.primitive_le_quadratic_after_anchor
    (show (19/50:ℝ)∈Icc 0 1 by constructor <;> norm_num) hanchor
  have hstart := h.primitive_eq_quadratic_on_line (by norm_num : (0:ℝ)≤19/50)
    (by norm_num : (19/50:ℝ)≤391/500) (by norm_num : (391/500:ℝ)≤1)
    hanchor hline (391/500) ⟨by norm_num,le_rfl⟩
  have hD (z : ℝ) (hz : z∈Icc (391/500:ℝ) 1) :
      0≤Variational.quadratic lam z-S-curvePrimitive phi z := by
    have hh := hprimitive z ⟨by linarith only [hz.1],hz.2⟩
    linarith only [hh]
  have hdefect := h.fixedControl_linear_defect_lower (by norm_num : (0:ℝ)≤391/500)
    (le_refl (1:ℝ)) halpha hslope hcross hD hcontrol
  exact h.intermediateSmallMass_test hlam hS hp hc hhead hcap
    (fun z hz => hline z ⟨by linarith only [hz.1,hlam.1],hz.2⟩)
    hfall hstart hprimitive hdefect hn

end VerifierCurve
end OptimalG
