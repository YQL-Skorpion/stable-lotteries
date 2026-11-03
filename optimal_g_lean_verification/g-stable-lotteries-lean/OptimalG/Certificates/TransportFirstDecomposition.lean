import OptimalG.Certificates.ReferenceFirstVariation

/-! The first-order coefficient term along the actual three-variable chord
splits into the scalar auxiliary-ODE forcing and the two rank forces. All
three are derivatives of the same frozen rational expression. -/
namespace OptimalG.Certificates.Transport
open RatExpr
open scoped BigOperators
namespace FrozenParameters

theorem logGradient_three (e : E) (x : Fin 16→ℝ) (s r a : ℝ) :
    logGradient e x (threeDirection s r a)=
      s*logGradient e x (coordinateDirection 0)+
      r*logGradient e x (coordinateDirection 1)+
      a*logGradient e x (coordinateDirection 2) := by
  rw [logGradient_coordinate,logGradient_coordinate,logGradient_coordinate]
  simp [logGradient,threeDirection,Fin.sum_univ_succ]
  ring

theorem sourceFirst_three (d : FrozenParameters) (late : Bool) (i : Fin 4)
    (x : Fin 16→ℝ) (s r a : ℝ) :
    d.sourceFirst late i x (threeDirection s r a)=
      s*d.sourceFirst late i x (coordinateDirection 0)+
      r*d.sourceFirst late i x (coordinateDirection 1)+
      a*d.sourceFirst late i x (coordinateDirection 2) := by
  simp only [sourceFirst,logGradient_three]
  ring

theorem weightedFirst_three (d : FrozenParameters) (late : Bool)
    (weights : Fin 4→ℝ) (x : Fin 16→ℝ) (s r a : ℝ) :
    d.weightedFirst late weights x (threeDirection s r a)=
      s*d.weightedFirst late weights x (coordinateDirection 0)+
      r*d.weightedFirst late weights x (coordinateDirection 1)+
      a*d.weightedFirst late weights x (coordinateDirection 2) := by
  calc
    _=∑ i∈activeTerms late,
        (s*(weights i*d.sourceFirst late i x (coordinateDirection 0))+
        r*(weights i*d.sourceFirst late i x (coordinateDirection 1))+
        a*(weights i*d.sourceFirst late i x (coordinateDirection 2))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sourceFirst_three]
      ring
    _=_ := by simp only [Finset.sum_add_distrib,←Finset.mul_sum,weightedFirst]

end FrozenParameters
namespace ReferenceScalarCell

theorem weightedFirst_three_forces (c : ReferenceScalarCell)
    (t factor Z ds eR eA : ℝ) (weights : Fin 4→ℝ)
    (hregular : ∀ i∈FrozenParameters.activeTerms c.flow.late,
      c.params.sourceRegular c.flow.late i (c.frozenInput t))
    (hweight : ∀ i∈FrozenParameters.activeTerms c.flow.late,
      weights i=factor*FrozenParameters.referencePower Z i*
        (c.params.coefficients c.flow.late i).eval (c.frozenInput t)) :
    c.params.weightedFirst c.flow.late weights (c.frozenInput t)
        (FrozenParameters.threeDirection ds eR eA)=
      ds*(factor*(Z*c.actualAlphaS t+c.actualBetaS t))+
      eR*(factor*(Z*(partialExpr 1 c.alphaSource).eval (c.frozenInput t)+
        (partialExpr 1 c.betaSource).eval (c.frozenInput t)))+
      eA*(factor*(Z*(partialExpr 2 c.alphaSource).eval (c.frozenInput t)+
        (partialExpr 2 c.betaSource).eval (c.frozenInput t))) := by
  rw [FrozenParameters.weightedFirst_three,
    c.weightedFirst_force t factor Z 0 weights hregular hweight,
    c.weightedFirst_force t factor Z 1 weights hregular hweight,
    c.weightedFirst_force t factor Z 2 weights hregular hweight]
  rfl

end ReferenceScalarCell
end OptimalG.Certificates.Transport
