import OptimalG.Certificates.ExpressionTaylorResidual
import OptimalG.Certificates.TransportCoefficients
import OptimalG.Certificates.TransportSegments
import OptimalG.Certificates.CapCubic
import OptimalG.Certificates.RationalCalculus

/-! The residual checked for each reference-flow cubic is the residual of the
actual early/late affine control equation. Reference ranks are the original
affine maps, and each low-score branch is either the cap or an exact cubic. -/
namespace OptimalG.Certificates
namespace RatExpr

def polynomial {n : ℕ} (p : RationalPolynomial) (x : RatExpr n) : RatExpr n :=
  match p with
  | [] => 0
  | a::p => .const a+x*polynomial p x

theorem polynomial_eval {n : ℕ} (p : RationalPolynomial) (x : RatExpr n) (v : Fin n→ℝ) :
    (polynomial p x).eval v=p.eval (x.eval v) := by
  induction p with
  | nil => simp [polynomial,eval,RationalPolynomial.eval]
  | cons a p ih => simp only [polynomial,eval_addNotation,eval_mulNotation,eval,ih,RationalPolynomial.eval]

end RatExpr
namespace Transport
open RatExpr

structure ReferenceFlowCell where
  lam : ℚ
  slack : ℚ
  level : ℚ
  segment : ReferenceSegment
  late : Bool
  rPiece : Option CubicPiece
  aPiece : Option CubicPiece
  valuePolynomial : RationalPolynomial

namespace ReferenceFlowCell
abbrev E := RatExpr 1

def length (c : ReferenceFlowCell) : ℚ := c.segment.right.z-c.segment.left.z
def affineExpr (lo hi : ℚ) : E := .const lo+.const (hi-lo)*.var 0
def rankR (c : ReferenceFlowCell) : E := affineExpr c.segment.left.r c.segment.right.r
def rankA (c : ReferenceFlowCell) : E := affineExpr c.segment.left.a c.segment.right.a
def highRank (c : ReferenceFlowCell) : E := affineExpr c.segment.left.z c.segment.right.z

def scoreExpr (L S : ℚ) (p : Option CubicPiece) (r : E) : E :=
  match p with
  | none => .const (L/2)-.const (L*S)/((1-r)*(1-r))
  | some p => RatExpr.polynomial [p.a0,p.a1,p.a2,p.a3] (r-.const p.lo)

def primitiveExpr (L S : ℚ) (p : Option CubicPiece) (r : E) : E :=
  match p with
  | none => .const (L*L-L/2)+.const (L/2)*r-.const (L*S)/(1-r)
  | some p => RatExpr.polynomial [p.f0,p.a0,p.a1/2,p.a2/3,p.a3/4] (r-.const p.lo)

noncomputable def localScore (L S : ℝ) (p : Option CubicPiece) (r : ℝ) : ℝ :=
  match p with
  | none => capSlope L S r
  | some p => p.score (r-p.lo)

noncomputable def localPrimitive (L S : ℝ) (p : Option CubicPiece) (r : ℝ) : ℝ :=
  match p with
  | none => cap L S r
  | some p => p.primitive (r-p.lo)

theorem scoreExpr_eval (L S : ℚ) (p : Option CubicPiece) (r : E) (v : Fin 1→ℝ) :
    (scoreExpr L S p r).eval v=localScore L S p (r.eval v) := by
  cases p <;>
    simp [scoreExpr,localScore,RatExpr.polynomial_eval,RationalPolynomial.eval,
      eval_addNotation,eval_subNotation,eval_mulNotation,eval_divNotation,eval,
      capSlope,CubicPiece.score,pow_two,pow_succ] <;> ring

theorem primitiveExpr_eval (L S : ℚ) (p : Option CubicPiece) (r : E) (v : Fin 1→ℝ) :
    (primitiveExpr L S p r).eval v=localPrimitive L S p (r.eval v) := by
  cases p <;>
    simp [primitiveExpr,localPrimitive,RatExpr.polynomial_eval,RationalPolynomial.eval,
      eval_addNotation,eval_subNotation,eval_mulNotation,eval_divNotation,eval,
      cap,CubicPiece.primitive,pow_two,pow_succ] <;> ring

def Rexpr (c : ReferenceFlowCell) : E := primitiveExpr c.lam c.slack c.rPiece c.rankR
def scoreR (c : ReferenceFlowCell) : E := scoreExpr c.lam c.slack c.rPiece c.rankR
def scoreA (c : ReferenceFlowCell) : E := scoreExpr c.lam c.slack c.aPiece c.rankA
def Qexpr (c : ReferenceFlowCell) (r : E) : E := .const c.lam*r-.const (1/2)*r*r
def Pexpr (c : ReferenceFlowCell) : E := c.Qexpr (1-c.rankR)-.const c.slack
def Kexpr (c : ReferenceFlowCell) : E := c.Qexpr (c.highRank-c.rankR)-.const c.level
def hExpr (c : ReferenceFlowCell) : E := .const (2*c.lam)-c.rankA
def kExpr (c : ReferenceFlowCell) : E :=
  if c.late then 2*c.rankR-.const c.lam else c.rankR+c.rankA-.const c.lam
def denominatorExpr (c : ReferenceFlowCell) : E := c.hExpr*c.Rexpr-c.kExpr*c.Pexpr

def alphaExpr (c : ReferenceFlowCell) : E :=
  if c.late then (c.hExpr*c.scoreR+c.kExpr*c.scoreA)/c.denominatorExpr
  else (.const c.lam+c.rankR)*c.scoreA/c.denominatorExpr

def betaExpr (c : ReferenceFlowCell) : E :=
  if c.late then
    (((c.highRank-.const c.lam)*c.Pexpr+c.hExpr*c.Kexpr)*c.scoreR+
      ((c.highRank-.const c.lam)*c.Rexpr+c.kExpr*c.Kexpr)*c.scoreA)/c.denominatorExpr
  else ((c.highRank-.const c.lam)*(c.Rexpr+c.Pexpr)+
    (.const c.lam+c.rankR)*c.Kexpr)*c.scoreA/c.denominatorExpr

noncomputable def actualAlpha (c : ReferenceFlowCell) (t : ℝ) : ℝ :=
  let r:=c.rankR.evalOne t
  let a:=c.rankA.evalOne t
  let R:=localPrimitive c.lam c.slack c.rPiece r
  let A:=localScore c.lam c.slack c.aPiece a
  let B:=localScore c.lam c.slack c.rPiece r
  if c.late then lateAlpha c.lam c.slack r a R A B
  else earlyAlpha c.lam c.slack r a R A

noncomputable def actualBeta (c : ReferenceFlowCell) (t : ℝ) : ℝ :=
  let r:=c.rankR.evalOne t
  let a:=c.rankA.evalOne t
  let z:=c.highRank.evalOne t
  let R:=localPrimitive c.lam c.slack c.rPiece r
  let A:=localScore c.lam c.slack c.aPiece a
  let B:=localScore c.lam c.slack c.rPiece r
  if c.late then lateBeta c.lam c.level c.slack z r a R A B
  else earlyBeta c.lam c.level c.slack z r a R A

theorem Qexpr_eval (c : ReferenceFlowCell) (r : E) (v : Fin 1→ℝ) :
    (c.Qexpr r).eval v=quadratic c.lam (r.eval v) := by
  simp [Qexpr,eval_addNotation,eval_subNotation,eval_mulNotation,eval,quadratic]
  ring

theorem alphaExpr_eval (c : ReferenceFlowCell) (t : ℝ) :
    c.alphaExpr.evalOne t=c.actualAlpha t := by
  cases hl : c.late <;>
    simp [alphaExpr,actualAlpha,hl,denominatorExpr,hExpr,kExpr,Pexpr,Rexpr,scoreR,scoreA,
      evalOne,scoreExpr_eval,primitiveExpr_eval,Qexpr_eval,eval_addNotation,eval_subNotation,
      eval_mulNotation,eval_divNotation,eval_natNotation,eval,lateAlpha,earlyAlpha,
      lateDenominator,earlyDenominator,lateNumerator0,lateNumerator1,earlyNumerator0,
      h,lateK,earlyK,P]

theorem betaExpr_eval (c : ReferenceFlowCell) (t : ℝ) :
    c.betaExpr.evalOne t=c.actualBeta t := by
  cases hl : c.late <;>
    simp [betaExpr,actualBeta,hl,denominatorExpr,hExpr,kExpr,Pexpr,Kexpr,Rexpr,scoreR,scoreA,
      evalOne,scoreExpr_eval,primitiveExpr_eval,Qexpr_eval,eval_addNotation,eval_subNotation,
      eval_mulNotation,eval_divNotation,eval_natNotation,eval,lateBeta,earlyBeta,
      lateDenominator,earlyDenominator,lateNumerator2,lateNumerator3,earlyNumerator1,
      h,lateK,earlyK,P,K]

def valueExpr (c : ReferenceFlowCell) : E := RatExpr.polynomial c.valuePolynomial (.var 0)
def slopeExpr (c : ReferenceFlowCell) : E :=
  .const (1/c.length)*RatExpr.polynomial c.valuePolynomial.derivative (.var 0)
def residualExpr (c : ReferenceFlowCell) : E := c.slopeExpr-c.alphaExpr*c.valueExpr-c.betaExpr

theorem residualExpr_eval (c : ReferenceFlowCell) (t : ℝ) :
    c.residualExpr.evalOne t=c.valuePolynomial.derivative.eval t/(c.length:ℝ)-
      c.actualAlpha t*c.valuePolynomial.eval t-c.actualBeta t := by
  simp only [residualExpr,evalOne,eval_subNotation,eval_mulNotation,slopeExpr,
    valueExpr,RatExpr.polynomial_eval,eval,Rat.cast_div,Rat.cast_one]
  rw [show c.alphaExpr.eval (fun _ => t)=c.actualAlpha t from c.alphaExpr_eval t,
    show c.betaExpr.eval (fun _ => t)=c.actualBeta t from c.betaExpr_eval t]
  ring

theorem checked_residual {scale : ℕ} (hs : 0<scale) (c : ReferenceFlowCell) (bound : ℤ)
    (hc : c.residualExpr.midpointTaylorCheck scale bound=true) {t : ℝ}
    (ht : t∈Set.Icc (0:ℝ) 1) :
    |c.valuePolynomial.derivative.eval t/(c.length:ℝ)-
      c.actualAlpha t*c.valuePolynomial.eval t-c.actualBeta t|≤(bound:ℝ)/(scale:ℝ) := by
  rw [←residualExpr_eval]
  exact RatExpr.midpointTaylorCheck_sound hs c.residualExpr bound hc ht

def alphaUpperCheck (scale : ℕ) (c : ReferenceFlowCell) (upper : ℚ) : Bool :=
  (.const upper-c.alphaExpr).integerLowerCheck scale
    (fun _ => IntegerInterval.fromRat scale ⟨0,1⟩) 0

theorem alphaUpperCheck_sound {scale : ℕ} (hs : 0<scale) (c : ReferenceFlowCell) (upper : ℚ)
    (hc : c.alphaUpperCheck scale upper=true) {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) :
    c.actualAlpha t<(upper:ℝ) := by
  have h := RatExpr.integerLowerCheck_sound hs ((.const upper:E)-c.alphaExpr)
    (fun _ => IntegerInterval.fromRat scale ⟨0,1⟩) 0 hc (fun _ => t) (by
      intro i
      apply IntegerInterval.fromRat_contains hs
      simpa [RatInterval.Contains] using ht)
  simp only [Int.cast_zero,zero_div,eval_subNotation,eval] at h
  change 0<(upper:ℝ)-c.alphaExpr.evalOne t at h
  rw [alphaExpr_eval] at h
  exact sub_pos.mp h

end ReferenceFlowCell
end Transport
end OptimalG.Certificates
