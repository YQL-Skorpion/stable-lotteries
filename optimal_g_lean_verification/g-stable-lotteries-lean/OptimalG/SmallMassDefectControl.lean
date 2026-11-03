import OptimalG.FixedControlDeficit
import OptimalG.DefectBounds

/-! Two scalar facts about one fixed control imply the entire score-defect
lower bound used in the intermediate small-mass strip. -/
namespace OptimalG
open Set

namespace VerifierCurve

theorem fixedControl_linear_defect_lower {phi : ℝ→ℝ}
    {lam S p theta alpha a b c k : ℝ}
    (h : VerifierCurve phi lam) (ha : 0≤a) (hb : b≤1) (halpha : 0≤alpha)
    (hslope : k≤theta-1+alpha*p)
    (hanchor : 0≤(theta-1+alpha*p)*(c-lam)-alpha*p^2/2)
    (hD : ∀ r∈Icc a b,0≤Variational.quadratic lam r-S-curvePrimitive phi r)
    (hcontrol : ∀ r∈Icc a b,phi r≤
      -theta*(r-lam)-alpha*(Variational.quadratic lam (r-p)-S-curvePrimitive phi r)) :
    ∀ r∈Icc a b,k*max (r-c) 0≤scoreDefect phi lam r := by
  intro r hr
  by_cases hrc : r≤c
  · rw [max_eq_right (sub_nonpos.mpr hrc),mul_zero]
    exact h.scoreDefect_nonneg ⟨ha.trans hr.1,hr.2.trans hb⟩
  · have hcr : 0≤r-c := sub_nonneg.mpr (lt_of_not_ge hrc).le
    have hh := hcontrol r hr
    have hscale := mul_nonneg halpha (hD r hr)
    have hm := mul_le_mul_of_nonneg_right hslope hcr
    have hid := control_deficit_identity lam S p theta alpha (curvePrimitive phi r) r
    rw [max_eq_left hcr]
    dsimp [scoreDefect]
    nlinarith only [hh,hscale,hm,hid,hanchor]

end VerifierCurve
end OptimalG
