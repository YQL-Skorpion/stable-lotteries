import OptimalG.CapHeadSlopeOrder
import OptimalG.IntermediateSelectedAssembly
import OptimalG.LineControlDeficit
import OptimalG.CubicControlDeficit

/-! The selected-region scalar certificates use the actual fixed line
control. Its differential inequality supplies the cubic bound, including
ranks before the crossing where the unclipped cubic is negative. -/
namespace OptimalG
open Set Variational

noncomputable def intermediateSelectedDeficit (lam S z : ℝ) : ℝ :=
  cubicControlDeficit (Certificates.LineControl.slope lam S)
    (Certificates.LineControl.alpha lam S) (Certificates.LineControl.crossing lam S) z

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- Actual fixed-control dynamics discharge the score-deficit hypothesis of
the finite selected-region checker. -/
theorem intermediate_selected_of_fixed_line {S c p z : ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (hp : p∈Icc lam (13/20:ℝ)) (hz : z∈Icc (391/500:ℝ) (7/8))
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial lam S)
    (hline : ∀ r∈Icc (9/25:ℝ) (391/500),phi r=lam-r)

    (harea : binarySlackArea phi lam S (7/20)≤87/1000000000)
    (hcontrol : ∀ r∈Icc (391/500:ℝ) 1,phi r≤
      -Certificates.LineControl.theta lam S*(r-lam)-Certificates.LineControl.alpha lam S*
        (quadratic lam (r-9/25)-S-curvePrimitive phi r))
    (hn : IntermediateSelectedSigns lam S p z (intermediateSelectedDeficit lam S z)) :
    ∀ q∈Icc (0:ℝ) lam,z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+
      intermediateEta phi lam (527/2000) p*phi z≤0 := by
  have hL : lam∈Icc (22493/40000:ℝ) (56233/100000) := by
    constructor <;> linarith only [g.lambda_mem.1,g.lambda_mem.2]
  have hcapOrder := capHeadSlopeOrder hL hS
  have hanchor := g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩
  have hstart := h.primitive_eq_quadratic_on_line (by norm_num : (0:ℝ)≤9/25)
    (by norm_num : (9/25:ℝ)≤391/500) (by norm_num : (391/500:ℝ)≤1) hanchor hline
    (391/500) ⟨by norm_num,le_rfl⟩
  have hcap : ∀ r∈Icc (391/500:ℝ) 1,curvePrimitive phi r≤quadratic lam r-S := by
    intro r hr
    exact h.primitive_le_quadratic_after_anchor (a:=9/25) (by norm_num) hanchor
      r ⟨by linarith only [hr.1],hr.2⟩
  have hh := (h.lineControl_deficits hL hS hcap hcontrol).2 z
    ⟨hz.1,by linarith only [hz.2]⟩
  have hm : 0<Certificates.LineControl.slope lam S := div_pos
    (Certificates.LineControl.slopeNumerator_pos hL hS) (Certificates.LineControl.denominator_pos hL hS)
  have he : intermediateSelectedDeficit lam S z≤scoreDefect phi lam z := by
    apply (cubicControlDeficit_le_clipped hm (Certificates.LineControl.alpha lam S)
      (Certificates.LineControl.crossing lam S) z).trans
    exact hh
  exact h.intermediate_selected_of_signs g hS hc hp hz hinitial hstart
    (hline (391/500) ⟨by norm_num,le_rfl⟩) hcapOrder harea he hn

end VerifierCurve
end OptimalG
