import OptimalG.Certificates.ReferenceScalarExpressions
import OptimalG.Certificates.ReferenceProfileCell

/-! The profile bounds used by a Hessian certificate are bounds for the
actual frozen expression inputs. The gauge polynomial is composed with the
same affine reference rank map, preserving its exact real evaluation. -/
namespace OptimalG.Certificates.Transport.ReferenceScalarCell
open Set RatExpr

theorem gaugePolynomialExpr_eval (c : ReferenceScalarCell) (p : RationalPolynomial)
    (lo hi : ℚ) (t : ℝ) :
    (c.gaugePolynomialExpr p lo hi).evalOne t=
      p.eval (((ReferenceFlowCell.affineExpr lo hi).evalOne t-c.leftContact)/
        ((c.rightContact:ℝ)-c.leftContact)) := by
  simp only [gaugePolynomialExpr,evalOne,RatExpr.polynomial_eval,RatExpr.eval,
    RationalPolynomial.eval_compose,RationalPolynomial.eval,
    ReferenceFlowCell.affineExpr,eval_addNotation,eval_mulNotation,
    Rat.cast_div,Rat.cast_sub]
  congr 1
  ring

def rProfile (c : ReferenceScalarCell) (bounds : ReferenceProfileBox) : ReferenceProfileCell :=
  ⟨c.flow.lam,c.flow.slack,c.leftContact,c.rightContact,
    c.flow.segment.left.r,c.flow.segment.right.r,c.flow.rPiece,c.gauge,c.gaugeDerivative,bounds⟩

def aProfile (c : ReferenceScalarCell) (bounds : ReferenceProfileBox) : ReferenceProfileCell :=
  ⟨c.flow.lam,c.flow.slack,c.leftContact,c.rightContact,
    c.flow.segment.left.a,c.flow.segment.right.a,c.flow.aPiece,c.gauge,c.gaugeDerivative,bounds⟩

theorem rProfile_gauge (c : ReferenceScalarCell) (bounds : ReferenceProfileBox) (t : ℝ) :
    (c.rProfile bounds).localGauge (c.flow.rankR.evalOne t)=c.rGauge.evalOne t ∧
    (c.rProfile bounds).localGaugeDerivative (c.flow.rankR.evalOne t)=c.rGaugeDerivative.evalOne t := by
  cases hp : c.flow.rPiece with
  | none =>
    simp [rProfile,ReferenceProfileCell.localGauge,ReferenceProfileCell.localGaugeDerivative,
      rGauge,rGaugeDerivative,gaugeExpr,gaugeDerivativeExpr,hp,evalOne,
      eval_divNotation,eval_subNotation,eval_mulNotation,eval,pow_two]
  | some p =>
    simp [rProfile,ReferenceProfileCell.localGauge,ReferenceProfileCell.localGaugeDerivative,
      rGauge,rGaugeDerivative,gaugeExpr,gaugeDerivativeExpr,hp,gaugePolynomialExpr_eval,
      ReferenceFlowCell.rankR]

theorem aProfile_gauge_derivative (c : ReferenceScalarCell) (bounds : ReferenceProfileBox) (t : ℝ) :
    (c.aProfile bounds).localGaugeDerivative (c.flow.rankA.evalOne t)=
      c.aGaugeDerivative.evalOne t := by
  cases hp : c.flow.aPiece with
  | none =>
    simp [aProfile,ReferenceProfileCell.localGaugeDerivative,aGaugeDerivative,
      gaugeDerivativeExpr,hp,evalOne,eval_divNotation,eval_subNotation,eval_mulNotation,eval,pow_two]
  | some p =>
    simp only [aProfile,ReferenceProfileCell.localGaugeDerivative,aGaugeDerivative,
      gaugeDerivativeExpr,hp,gaugePolynomialExpr_eval,ReferenceFlowCell.rankA]

theorem checked_rProfile_coordinates {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceScalarCell) (bounds : ReferenceProfileBox)
    (hc : (c.rProfile bounds).check s k=true)
    (horder : c.flow.segment.left.r≤c.flow.segment.right.r)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    bounds.primitive.Contains s (c.frozenInput t 3) ∧
    bounds.score.Contains s (c.frozenInput t 7) ∧
    bounds.gauge.Contains s (c.frozenInput t 4) ∧
    bounds.gaugeDerivative.Contains s (c.frozenInput t 8) := by
  have hr := ReferenceFlowCell.affineExpr_mem horder ht
  change c.flow.rankR.evalOne t ∈ Icc (c.flow.segment.left.r:ℝ) c.flow.segment.right.r at hr
  have hh := (c.rProfile bounds).checked_profiles hs hk hc hr
  rw [(c.rProfile_gauge bounds t).1,(c.rProfile_gauge bounds t).2] at hh
  simpa [rProfile,frozenInput,frozenSubstitution,
    Matrix.cons_val_zero,Matrix.cons_val_succ,evalOne,
    ReferenceFlowCell.Rexpr,ReferenceFlowCell.scoreR,
    ReferenceFlowCell.primitiveExpr_eval,ReferenceFlowCell.scoreExpr_eval] using hh

theorem checked_aProfile_coordinates {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceScalarCell) (bounds : ReferenceProfileBox)
    (hc : (c.aProfile bounds).check s k=true)
    (horder : c.flow.segment.left.a≤c.flow.segment.right.a)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    bounds.score.Contains s (c.frozenInput t 9) ∧
    bounds.gaugeDerivative.Contains s (c.frozenInput t 10) := by
  have hr := ReferenceFlowCell.affineExpr_mem horder ht
  change c.flow.rankA.evalOne t ∈ Icc (c.flow.segment.left.a:ℝ) c.flow.segment.right.a at hr
  have hh := (c.aProfile bounds).checked_profiles hs hk hc hr
  rw [c.aProfile_gauge_derivative bounds t] at hh
  simpa [aProfile,frozenInput,frozenSubstitution,
    Matrix.cons_val_zero,Matrix.cons_val_succ,evalOne,
    ReferenceFlowCell.scoreA,ReferenceFlowCell.scoreExpr_eval] using And.intro hh.2.1 hh.2.2.2

end OptimalG.Certificates.Transport.ReferenceScalarCell
