import OptimalG.Certificates.Expression

/-! Substitution preserves the ordinary real interpretation of reified
rational expressions, including Lean's total division convention. -/
namespace OptimalG.Certificates.RatExpr

def substitute {n m : ℕ} (inputs : Fin n→RatExpr m) : RatExpr n→RatExpr m
  | .const q => .const q
  | .var i => inputs i
  | .neg e => .neg (substitute inputs e)
  | .add e f => .add (substitute inputs e) (substitute inputs f)
  | .mul e f => .mul (substitute inputs e) (substitute inputs f)
  | .inv e => .inv (substitute inputs e)

theorem substitute_eval {n m : ℕ} (inputs : Fin n→RatExpr m) (e : RatExpr n)
    (x : Fin m→ℝ) :
    (e.substitute inputs).eval x=e.eval (fun i => (inputs i).eval x) := by
  induction e with
  | const q => rfl
  | var i => rfl
  | neg e ih => simp only [substitute,eval,ih]
  | add e f ihe ihf => simp only [substitute,eval,ihe,ihf]
  | mul e f ihe ihf => simp only [substitute,eval,ihe,ihf]
  | inv e ih => simp only [substitute,eval,ih]

end OptimalG.Certificates.RatExpr
