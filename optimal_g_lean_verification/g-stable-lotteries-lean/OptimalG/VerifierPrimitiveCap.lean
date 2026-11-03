import OptimalG.BinarySmallCentral

/-! Once the actual primitive meets Q−S, the score ceiling controls the whole
remaining primitive, and every straight segment keeps exact equality. -/
namespace OptimalG
open Set MeasureTheory

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem primitive_le_quadratic_after_anchor {a S : ℝ}
    (ha : a∈Icc (0:ℝ) 1)
    (hanchor : curvePrimitive phi a=Variational.quadratic lam a-S) :
    ∀ r∈Icc a 1,curvePrimitive phi r≤Variational.quadratic lam r-S := by
  intro r hr
  have hh := h.primitive_relative_quadratic_antitone ha ⟨ha.1.trans hr.1,hr.2⟩ hr.1
  dsimp only at hh
  rw [hanchor] at hh
  linarith only [hh]

theorem primitive_eq_quadratic_on_line {a b S : ℝ}
    (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hanchor : curvePrimitive phi a=Variational.quadratic lam a-S)
    (hline : ∀ r∈Icc a b,phi r=lam-r) :
    ∀ r∈Icc a b,curvePrimitive phi r=Variational.quadratic lam r-S := by
  intro r hr
  have hi : (∫ u in a..r,phi u)=∫ u in a..r,lam-u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hr.1] at hu
    exact hline u ⟨hu.1,hu.2.trans hr.2⟩
  rw [←h.primitive_difference ha hr.1 (hr.2.trans hb),Variational.integral_line,hanchor] at hi
  linarith only [hi]

end VerifierCurve
end OptimalG
