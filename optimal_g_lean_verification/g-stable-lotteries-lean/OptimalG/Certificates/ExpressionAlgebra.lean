import OptimalG.Certificates.Expression
namespace OptimalG.Certificates.RatExpr
variable {n : ℕ}
@[simp] theorem eval_addNotation (e f : RatExpr n) (x : Fin n→ℝ) :
    (e+f).eval x=e.eval x+f.eval x := rfl
@[simp] theorem eval_mulNotation (e f : RatExpr n) (x : Fin n→ℝ) :
    (e*f).eval x=e.eval x*f.eval x := rfl
@[simp] theorem eval_negNotation (e : RatExpr n) (x : Fin n→ℝ) :
    (-e).eval x= -e.eval x := rfl
@[simp] theorem eval_subNotation (e f : RatExpr n) (x : Fin n→ℝ) :
    (e-f).eval x=e.eval x-f.eval x := rfl
@[simp] theorem eval_divNotation (e f : RatExpr n) (x : Fin n→ℝ) :
    (e/f).eval x=e.eval x/f.eval x := rfl
@[simp] theorem eval_natNotation (k : ℕ) (x : Fin n→ℝ) :
    (OfNat.ofNat k : RatExpr n).eval x=(k:ℝ) := by
  change ((k:ℚ):ℝ)=(k:ℝ)
  exact Rat.cast_natCast k
end OptimalG.Certificates.RatExpr
