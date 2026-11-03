import OptimalG.Certificates.TransportFirstAlgebra
import OptimalG.Certificates.ReferenceScalarExpressions

/-! The four logarithmic terms combine exactly into the derivatives of the
same affine field used to construct the reference flow. This removes a
separate numerical premise for their scalar and positional first variations. -/
namespace OptimalG.Certificates.Transport
open RatExpr
open scoped BigOperators

namespace FrozenParameters

noncomputable def referencePower (Z : ℝ) (i : Fin 4) : ℝ :=
  if i.val<2 then Z else 1

theorem early_zero_partial (d : FrozenParameters) (j : Fin 16) (x : Fin 16→ℝ)
    (i : Fin 4) (hi : i=0 ∨ i=2) :
    (partialExpr j (d.coefficients false i)).eval x=0 := by
  rcases hi with rfl | rfl <;>
    change (partialExpr j (.mul (.mul (.mul d.j (.const 0)) _)
      (.inv (d.denominator false)))).eval x=0 <;>
    simp only [partial_mul_eval,partial_inv_eval,partial_const_eval,eval,
      Rat.cast_zero,mul_zero,zero_mul,add_zero,zero_add]

/-- Both early zero terms remain identically zero after any actual coordinate
partial. The common four-term grouping therefore also applies on that branch. -/
theorem active_first_sum (d : FrozenParameters) (late : Bool) (j : Fin 16)
    (x : Fin 16→ℝ) (Z : ℝ) :
    (∑ i∈activeTerms late,referencePower Z i*(partialExpr j (d.coefficients late i)).eval x)=
      Z*(partialExpr j (d.coefficients late 0+d.coefficients late 1)).eval x+
        (partialExpr j (d.coefficients late 2+d.coefficients late 3)).eval x := by
  have hz0 := d.early_zero_partial j x 0 (Or.inl rfl)
  have hz2 := d.early_zero_partial j x 2 (Or.inr rfl)
  have hplus (e f : RatExpr 16) : (partialExpr j (e+f)).eval x =
      (partialExpr j e).eval x+(partialExpr j f).eval x := partial_add_eval j e f x
  cases late <;>
    simp [activeTerms,referencePower,Fin.sum_univ_succ,hplus,hz0,hz2] <;> ring

theorem weightedFirst_affine (d : FrozenParameters) (late : Bool)
    (x : Fin 16→ℝ) (j : Fin 16) (factor Z : ℝ) (weights : Fin 4→ℝ)
    (hregular : ∀ i∈activeTerms late,d.sourceRegular late i x)
    (hweight : ∀ i∈activeTerms late,
      weights i=factor*referencePower Z i*(d.coefficients late i).eval x) :
    d.weightedFirst late weights x (coordinateDirection j)=
      factor*(Z*(partialExpr j (d.coefficients late 0+d.coefficients late 1)).eval x+
        (partialExpr j (d.coefficients late 2+d.coefficients late 3)).eval x) := by
  rw [d.weightedFirst_combined late x j factor (referencePower Z) weights hregular hweight,
    d.active_first_sum late j x Z]

end FrozenParameters
namespace ReferenceScalarCell

/-- Coordinates 0,1,2 give, respectively, the actual scalar forcing and the
two positional forces used by the reference transport certificate. -/
theorem weightedFirst_force (c : ReferenceScalarCell) (t factor Z : ℝ) (j : Fin 16)
    (weights : Fin 4→ℝ)
    (hregular : ∀ i∈FrozenParameters.activeTerms c.flow.late,
      c.params.sourceRegular c.flow.late i (c.frozenInput t))
    (hweight : ∀ i∈FrozenParameters.activeTerms c.flow.late,
      weights i=factor*FrozenParameters.referencePower Z i*
        (c.params.coefficients c.flow.late i).eval (c.frozenInput t)) :
    c.params.weightedFirst c.flow.late weights (c.frozenInput t)
        (FrozenParameters.coordinateDirection j)=
      factor*(Z*(partialExpr j c.alphaSource).eval (c.frozenInput t)+
        (partialExpr j c.betaSource).eval (c.frozenInput t)) :=
  c.params.weightedFirst_affine c.flow.late (c.frozenInput t) j factor Z weights
    hregular hweight

end ReferenceScalarCell
end OptimalG.Certificates.Transport
