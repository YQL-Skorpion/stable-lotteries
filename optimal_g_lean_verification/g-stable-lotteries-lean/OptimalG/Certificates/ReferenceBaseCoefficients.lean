import OptimalG.Certificates.ReferenceFlowExpressions
import OptimalG.Certificates.TransportFrozenExpressions
import OptimalG.Certificates.ExpressionSubstitution
import OptimalG.Certificates.ReferenceScalarExpressions

/-! The base values used in reference weights are the actual transported
coefficients at the reference scalar parameter. Gauge coordinates disappear
at that parameter, so they need not be re-evaluated for each weight bound. -/
namespace OptimalG.Certificates.Transport
open RatExpr

namespace FrozenParameters

theorem coefficients_reference_invariant (d : FrozenParameters) (late : Bool)
    (i : Fin 4) (x y : Fin 16→ℝ) (hx : x 0=d.referenceSlack) (hy : y 0=d.referenceSlack)
    (h1 : x 1=y 1) (h2 : x 2=y 2) (h3 : x 3=y 3) (h5 : x 5=y 5)
    (h7 : x 7=y 7) (h9 : x 9=y 9) :
    (d.coefficients late i).eval x=(d.coefficients late i).eval y := by
  rw [coefficients_eval,coefficients_eval]
  simp only [referenceHighRank,referencePrimitive,jacobian,shiftedScoreR,shiftedScoreA,
    hx,hy,sub_self,zero_mul,add_zero,h1,h2,h3,h5,h7,h9]

end FrozenParameters
namespace ReferenceFlowCell

def frozenParameters (c : ReferenceFlowCell) : FrozenParameters := ⟨c.lam,c.level,c.slack⟩

def baseSubstitution (c : ReferenceFlowCell) : Fin 16→E :=
  ![.const c.slack,c.rankR,c.rankA,c.Rexpr,0,c.highRank,0,c.scoreR,0,c.scoreA,0,0,0,0,0,0]

noncomputable def baseInput (c : ReferenceFlowCell) (t : ℝ) : Fin 16→ℝ :=
  fun i => (c.baseSubstitution i).evalOne t

def baseCoefficientExpr (c : ReferenceFlowCell) (i : Fin 4) : E :=
  (c.frozenParameters.coefficients c.late i).substitute c.baseSubstitution

theorem baseCoefficientExpr_eval (c : ReferenceFlowCell) (i : Fin 4) (t : ℝ) :
    (c.baseCoefficientExpr i).evalOne t=
      (c.frozenParameters.coefficients c.late i).eval (c.baseInput t) := by
  exact RatExpr.substitute_eval _ _ _

end ReferenceFlowCell

namespace ReferenceScalarCell

theorem base_coefficient_identity (c : ReferenceScalarCell) (i : Fin 4) (t : ℝ) :
    (c.flow.baseCoefficientExpr i).evalOne t=
      (c.params.coefficients c.flow.late i).eval (c.frozenInput t) := by
  rw [ReferenceFlowCell.baseCoefficientExpr_eval]
  apply FrozenParameters.coefficients_reference_invariant
  all_goals simp [ReferenceFlowCell.baseInput,ReferenceFlowCell.baseSubstitution,
    ReferenceFlowCell.frozenParameters,frozenInput,frozenSubstitution,params,evalOne,eval]

end ReferenceScalarCell
end OptimalG.Certificates.Transport
