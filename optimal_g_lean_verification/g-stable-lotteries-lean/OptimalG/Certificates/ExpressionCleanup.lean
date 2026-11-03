import OptimalG.Certificates.IntegerExpression
import OptimalG.Certificates.ExpressionAlgebra

/-! Exact algebraic cleanup before interval evaluation. This preserves real
values under Lean's total inverse convention. It deliberately does not claim
that validity of a simplified expression validates the original expression;
logarithmic factors must be checked separately. -/
namespace OptimalG.Certificates.RatExpr
variable {n : ℕ}

def cleanNeg : RatExpr n→RatExpr n
  | .const q => .const (-q)
  | .neg e => e
  | e => .neg e

def cleanAdd : RatExpr n→RatExpr n→RatExpr n
  | .const q,.const r => .const (q+r)
  | .const q,e => if q=0 then e else .add (.const q) e
  | e,.const q => if q=0 then e else .add e (.const q)
  | e,f => .add e f

def cleanMul : RatExpr n→RatExpr n→RatExpr n
  | .const q,.const r => .const (q*r)
  | .const q,e => if q=0 then .const 0 else if q=1 then e else .mul (.const q) e
  | e,.const q => if q=0 then .const 0 else if q=1 then e else .mul e (.const q)
  | e,f => .mul e f

def cleanInv : RatExpr n→RatExpr n
  | .const q => .const q⁻¹
  | .inv e => e
  | e => .inv e

def cleanup : RatExpr n→RatExpr n
  | .const q => .const q
  | .var i => .var i
  | .neg e => cleanNeg e.cleanup
  | .add e f => cleanAdd e.cleanup f.cleanup
  | .mul e f => cleanMul e.cleanup f.cleanup
  | .inv e => cleanInv e.cleanup

theorem cleanNeg_eval (e : RatExpr n) (x : Fin n→ℝ) :
    (cleanNeg e).eval x= -e.eval x := by
  cases e <;> simp [cleanNeg,eval]

theorem cleanAdd_eval (e f : RatExpr n) (x : Fin n→ℝ) :
    (cleanAdd e f).eval x=e.eval x+f.eval x := by
  cases e <;> cases f <;> simp only [cleanAdd] <;>
    (try split_ifs) <;> simp_all [eval]

theorem cleanMul_eval (e f : RatExpr n) (x : Fin n→ℝ) :
    (cleanMul e f).eval x=e.eval x*f.eval x := by
  cases e <;> cases f <;> simp only [cleanMul] <;>
    (try split_ifs) <;> simp_all [eval]

theorem cleanInv_eval (e : RatExpr n) (x : Fin n→ℝ) :
    (cleanInv e).eval x=(e.eval x)⁻¹ := by
  cases e <;> simp [cleanInv,eval]

theorem cleanup_eval (e : RatExpr n) (x : Fin n→ℝ) : e.cleanup.eval x=e.eval x := by
  induction e with
  | const q => rfl
  | var i => rfl
  | neg e ih => simp only [cleanup,cleanNeg_eval,ih,eval]
  | add e f ihe ihf => simp only [cleanup,cleanAdd_eval,ihe,ihf,eval]
  | mul e f ihe ihf => simp only [cleanup,cleanMul_eval,ihe,ihf,eval]
  | inv e ih => simp only [cleanup,cleanInv_eval,ih,eval]

theorem integerInterval_cleanup_sound {s : ℕ} (hs : 0<s) (box : Fin n→IntegerInterval)
    (x : Fin n→ℝ) (hx : ∀ i,(box i).Contains s (x i)) (e : RatExpr n)
    {out : IntegerInterval} (hc : e.cleanup.integerInterval s box=some out) :
    out.Contains s (e.eval x) := by
  simpa only [cleanup_eval] using integerInterval_sound hs box x hx e.cleanup hc

end OptimalG.Certificates.RatExpr
