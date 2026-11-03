import OptimalG.Certificates.ReferenceFlowExpressions
import OptimalG.Certificates.TransportFrozenExpressions
import OptimalG.Certificates.ExpressionSubstitution

/-! The scalar force for the auxiliary reference ODE is obtained by actual
symbolic partial differentiation of the same transported coefficients used by
the logarithmic Hessian proof. Gauge polynomials are composed exactly with
each affine rank map before interval evaluation. -/
namespace OptimalG.Certificates.Transport
open RatExpr

structure ReferenceScalarCell where
  flow : ReferenceFlowCell
  leftContact : ℚ
  rightContact : ℚ
  start : ℚ
  finish : ℚ
  gauge : RationalPolynomial
  gaugeDerivative : RationalPolynomial

namespace ReferenceScalarCell
abbrev E := RatExpr 1

def params (c : ReferenceScalarCell) : FrozenParameters :=
  ⟨c.flow.lam,c.flow.level,c.flow.slack⟩

def gaugePolynomialExpr (c : ReferenceScalarCell) (p : RationalPolynomial)
    (lo hi : ℚ) : E :=
  RatExpr.polynomial (p.compose [(lo-c.leftContact)/(c.rightContact-c.leftContact),
    (hi-lo)/(c.rightContact-c.leftContact)]) (.var 0)

def gaugeExpr (c : ReferenceScalarCell) (piece : Option CubicPiece)
    (rank : E) (lo hi : ℚ) : E :=
  match piece with
  | none => .const (-c.flow.lam)/(1-rank)
  | some _ => c.gaugePolynomialExpr c.gauge lo hi

def gaugeDerivativeExpr (c : ReferenceScalarCell) (piece : Option CubicPiece)
    (rank : E) (lo hi : ℚ) : E :=
  match piece with
  | none => .const (-c.flow.lam)/((1-rank)*(1-rank))
  | some _ => c.gaugePolynomialExpr c.gaugeDerivative lo hi

def rGauge (c : ReferenceScalarCell) : E :=
  c.gaugeExpr c.flow.rPiece c.flow.rankR c.flow.segment.left.r c.flow.segment.right.r
def rGaugeDerivative (c : ReferenceScalarCell) : E :=
  c.gaugeDerivativeExpr c.flow.rPiece c.flow.rankR c.flow.segment.left.r c.flow.segment.right.r
def aGaugeDerivative (c : ReferenceScalarCell) : E :=
  c.gaugeDerivativeExpr c.flow.aPiece c.flow.rankA c.flow.segment.left.a c.flow.segment.right.a
def warpDerivative (c : ReferenceScalarCell) : E := .const (-1/(c.finish-c.start))
def warp (c : ReferenceScalarCell) : E := c.warpDerivative*(c.flow.highRank-.const c.start)

def frozenSubstitution (c : ReferenceScalarCell) : Fin 16→E :=
  ![.const c.flow.slack,c.flow.rankR,c.flow.rankA,c.flow.Rexpr,c.rGauge,c.flow.highRank,
    c.warp,c.flow.scoreR,c.rGaugeDerivative,c.flow.scoreA,c.aGaugeDerivative,
    c.warpDerivative,0,0,0,0]

noncomputable def frozenInput (c : ReferenceScalarCell) (t : ℝ) : Fin 16→ℝ :=
  fun i => (c.frozenSubstitution i).evalOne t

def alphaSource (c : ReferenceScalarCell) : RatExpr 16 :=
  c.params.coefficients c.flow.late 0+c.params.coefficients c.flow.late 1
def betaSource (c : ReferenceScalarCell) : RatExpr 16 :=
  c.params.coefficients c.flow.late 2+c.params.coefficients c.flow.late 3

def alphaSExpr (c : ReferenceScalarCell) : E :=
  (partialExpr 0 c.alphaSource).substitute c.frozenSubstitution
def betaSExpr (c : ReferenceScalarCell) : E :=
  (partialExpr 0 c.betaSource).substitute c.frozenSubstitution

noncomputable def actualAlphaS (c : ReferenceScalarCell) (t : ℝ) : ℝ :=
  (partialExpr 0 c.alphaSource).eval (c.frozenInput t)
noncomputable def actualBetaS (c : ReferenceScalarCell) (t : ℝ) : ℝ :=
  (partialExpr 0 c.betaSource).eval (c.frozenInput t)

theorem alphaSExpr_eval (c : ReferenceScalarCell) (t : ℝ) :
    c.alphaSExpr.evalOne t=c.actualAlphaS t := by
  exact RatExpr.substitute_eval _ _ _

theorem betaSExpr_eval (c : ReferenceScalarCell) (t : ℝ) :
    c.betaSExpr.evalOne t=c.actualBetaS t := by
  exact RatExpr.substitute_eval _ _ _

def residualExpr (c : ReferenceScalarCell) (p : RationalPolynomial) : E :=
  .const (1/c.flow.length)*RatExpr.polynomial p.derivative (.var 0)-
    c.flow.alphaExpr*RatExpr.polynomial p (.var 0)-
    c.alphaSExpr*c.flow.valueExpr-c.betaSExpr

theorem residualExpr_eval (c : ReferenceScalarCell) (p : RationalPolynomial) (t : ℝ) :
    (c.residualExpr p).evalOne t=p.derivative.eval t/(c.flow.length:ℝ)-
      c.flow.actualAlpha t*p.eval t-c.actualAlphaS t*c.flow.valuePolynomial.eval t-
        c.actualBetaS t := by
  simp only [residualExpr,evalOne,eval_subNotation,eval_mulNotation,
    RatExpr.polynomial_eval,eval,Rat.cast_div,Rat.cast_one,ReferenceFlowCell.valueExpr]
  rw [show c.flow.alphaExpr.eval (fun _ => t)=c.flow.actualAlpha t from c.flow.alphaExpr_eval t,
    show c.alphaSExpr.eval (fun _ => t)=c.actualAlphaS t from c.alphaSExpr_eval t,
    show c.betaSExpr.eval (fun _ => t)=c.actualBetaS t from c.betaSExpr_eval t]
  ring

end ReferenceScalarCell
end OptimalG.Certificates.Transport
