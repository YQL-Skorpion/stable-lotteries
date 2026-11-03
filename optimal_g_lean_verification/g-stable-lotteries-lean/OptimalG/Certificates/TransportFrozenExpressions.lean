import OptimalG.Certificates.ExpressionHessian
import OptimalG.VariationalTransportTerms

/-! Reification over a whole reference segment. Reference values are real
inputs, not rounded constants. The first three coordinates vary along the
comparison chord; all remaining coordinates are held fixed during Taylor
expansion. The last four coordinates are the nonnegative reference weights. -/
namespace OptimalG.Certificates.Transport
open RatExpr

structure FrozenParameters where
  lam : ℚ
  level : ℚ
  referenceSlack : ℚ
  deriving DecidableEq,Repr

namespace FrozenParameters
abbrev E := RatExpr 16

def S : E := .var 0
def r : E := .var 1
def a : E := .var 2
/-- Coordinates 3..11: reference primitive, gauge, high rank, warp,
reference score at r, gauge derivative at r, score at a, gauge derivative at a,
and high-rank warp derivative. -/
def shift (d : FrozenParameters) : E := S-.const d.referenceSlack
def R (d : FrozenParameters) : E := .var 3+d.shift*.var 4
def z (d : FrozenParameters) : E := .var 5+d.shift*.var 6
def j (d : FrozenParameters) : E := 1+d.shift*.var 11
def mR (d : FrozenParameters) : E := .var 7+d.shift*.var 8
def mA (d : FrozenParameters) : E := .var 9+d.shift*.var 10

def Q (d : FrozenParameters) (u : E) : E := .const d.lam*u-.const (1/2)*u*u
def Pexpr (d : FrozenParameters) : E := d.Q (1-r)-S
def Kexpr (d : FrozenParameters) : E := d.Q (d.z-r)-.const d.level
def hExpr (d : FrozenParameters) : E := 2*.const d.lam-a
def kExpr (d : FrozenParameters) (late : Bool) : E :=
  if late then 2*r-.const d.lam else r+a-.const d.lam
def denominator (d : FrozenParameters) (late : Bool) : E := d.hExpr*d.R-d.kExpr late*d.Pexpr

def numerators (d : FrozenParameters) (late : Bool) : Fin 4→E :=
  if late then ![d.hExpr,d.kExpr true,
    (d.z-.const d.lam)*d.Pexpr+d.hExpr*d.Kexpr,
    (d.z-.const d.lam)*d.R+d.kExpr true*d.Kexpr]
  else ![0,.const d.lam+r,0,
    (d.z-.const d.lam)*(d.R+d.Pexpr)+(.const d.lam+r)*d.Kexpr]

def score (d : FrozenParameters) (i : Fin 4) : E :=
  if i=0 ∨ i=2 then d.mR else d.mA

def coefficients (d : FrozenParameters) (late : Bool) (i : Fin 4) : E :=
  d.j*d.numerators late i*d.score i/d.denominator late

def weight (i : Fin 4) : E := .var ⟨12+i.val,by omega⟩

noncomputable def referencePrimitive (d : FrozenParameters) (x : Fin 16→ℝ) : ℝ :=
  x 3+(x 0-d.referenceSlack)*x 4
noncomputable def referenceHighRank (d : FrozenParameters) (x : Fin 16→ℝ) : ℝ :=
  x 5+(x 0-d.referenceSlack)*x 6
noncomputable def jacobian (d : FrozenParameters) (x : Fin 16→ℝ) : ℝ :=
  1+(x 0-d.referenceSlack)*x 11
noncomputable def shiftedScoreR (d : FrozenParameters) (x : Fin 16→ℝ) : ℝ :=
  x 7+(x 0-d.referenceSlack)*x 8
noncomputable def shiftedScoreA (d : FrozenParameters) (x : Fin 16→ℝ) : ℝ :=
  x 9+(x 0-d.referenceSlack)*x 10

@[simp] theorem R_eval (d : FrozenParameters) (x : Fin 16→ℝ) :
    d.R.eval x=d.referencePrimitive x := rfl
@[simp] theorem z_eval (d : FrozenParameters) (x : Fin 16→ℝ) :
    d.z.eval x=d.referenceHighRank x := rfl
@[simp] theorem j_eval (d : FrozenParameters) (x : Fin 16→ℝ) :
    d.j.eval x=d.jacobian x := by simp [j,shift,S,eval,jacobian]
@[simp] theorem mR_eval (d : FrozenParameters) (x : Fin 16→ℝ) :
    d.mR.eval x=d.shiftedScoreR x := rfl
@[simp] theorem mA_eval (d : FrozenParameters) (x : Fin 16→ℝ) :
    d.mA.eval x=d.shiftedScoreA x := rfl

@[simp] theorem Q_eval (d : FrozenParameters) (u : E) (x : Fin 16→ℝ) :
    (d.Q u).eval x=quadratic d.lam (u.eval x) := by
  simp [Q,eval,quadratic]
  ring

/-- These are precisely the coefficients in the actual logarithmic control
comparison, including the moving high-rank Jacobian and score shift. -/
theorem coefficients_eval (d : FrozenParameters) (late : Bool) (i : Fin 4) (x : Fin 16→ℝ) :
    (d.coefficients late i).eval x=
      if late then Variational.lateLogCoefficients d.lam d.level (x 0)
        (d.referenceHighRank x) (x 1) (x 2) (d.referencePrimitive x)
        (d.jacobian x) (d.shiftedScoreR x) (d.shiftedScoreA x) i
      else Variational.earlyLogCoefficients d.lam d.level (x 0)
        (d.referenceHighRank x) (x 1) (x 2) (d.referencePrimitive x)
        (d.jacobian x) (d.shiftedScoreA x) i := by
  cases late <;> fin_cases i <;>
    simp [coefficients,numerators,score,denominator,hExpr,kExpr,Pexpr,Kexpr,Q_eval,
      S,r,a,eval,Variational.earlyLogCoefficients,Variational.lateLogCoefficients,
      earlyDenominator,lateDenominator,earlyNumerator0,earlyNumerator1,
      lateNumerator0,lateNumerator1,lateNumerator2,lateNumerator3,h,earlyK,lateK,P,K] <;> ring

/-- The factored logarithm avoids interval dependency from differentiating a
quotient and cancelling it afterwards. It is exactly the logarithm of the
actual coefficient when its factors are nonzero. -/
noncomputable def logSource (d : FrozenParameters) (late : Bool) (i : Fin 4)
    (x : Fin 16→ℝ) : ℝ :=
  Real.log (d.j.eval x)+Real.log ((d.numerators late i).eval x)+
    Real.log ((d.score i).eval x)-Real.log ((d.denominator late).eval x)

theorem logSource_eq (d : FrozenParameters) (late : Bool) (i : Fin 4) (x : Fin 16→ℝ)
    (hj : d.j.eval x≠0) (hn : (d.numerators late i).eval x≠0)
    (hm : (d.score i).eval x≠0) (hD : (d.denominator late).eval x≠0) :
    d.logSource late i x=Real.log ((d.coefficients late i).eval x) := by
  simp only [coefficients,eval_divNotation,eval_mulNotation]
  rw [Real.log_div (mul_ne_zero (mul_ne_zero hj hn) hm) hD,
    Real.log_mul (mul_ne_zero hj hn) hm,Real.log_mul hj hn]
  rfl

/-- Exact expressions for the symmetric Hessian of the weighted log source.
Only coordinates 0,1,2 vary in the chord. -/
def hessianEntry (d : FrozenParameters) (late : Bool) (u v : Fin 16) : E :=
  (if late then (List.finRange 4) else [1,3]).foldl (fun acc i => acc+weight i*
    (logHessian u v d.j+logHessian u v (d.numerators late i)+
      logHessian u v (d.score i)-logHessian u v (d.denominator late))) 0

end FrozenParameters
end OptimalG.Certificates.Transport
