import OptimalG.Certificates.Expression
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Symbolic differentiation of rational expressions, with a calculus proof.
The same exact expression and interval evaluator can therefore certify actual
first and second derivatives along transported comparison curves. -/
namespace OptimalG.Certificates.RatExpr
variable {n : ℕ}

/-- Every reciprocal in an expression has a nonzero denominator at the point. -/
noncomputable def Valid (x : Fin n → ℝ) : RatExpr n → Prop
  | .const _ => True
  | .var _ => True
  | .neg e => e.Valid x
  | .add e f => e.Valid x ∧ f.Valid x
  | .mul e f => e.Valid x ∧ f.Valid x
  | .inv e => e.Valid x ∧ e.eval x≠0

/-- Differentiate with prescribed expression-valued derivatives of the inputs. -/
def differentiate (ds : Fin n → RatExpr n) : RatExpr n → RatExpr n
  | .const _ => .const 0
  | .var i => ds i
  | .neg e => .neg (differentiate ds e)
  | .add e f => .add (differentiate ds e) (differentiate ds f)
  | .mul e f => .add (.mul (differentiate ds e) f) (.mul e (differentiate ds f))
  | .inv e => .neg (.mul (differentiate ds e) (.inv (.mul e e)))

theorem differentiate_valid (ds : Fin n → RatExpr n) {x : Fin n → ℝ}
    (hds : ∀ i,(ds i).Valid x) {e : RatExpr n} (he : e.Valid x) :
    (differentiate ds e).Valid x := by
  induction e with
  | const q => trivial
  | var i => exact hds i
  | neg e ih => exact ih he
  | add e f ihe ihf => exact ⟨ihe he.1,ihf he.2⟩
  | mul e f ihe ihf => exact ⟨⟨ihe he.1,he.2⟩,⟨he.1,ihf he.2⟩⟩
  | inv e ih => exact ⟨ih he.1,⟨⟨he.1,he.1⟩,mul_ne_zero he.2 he.2⟩⟩

/-- The symbolic derivative is the true derivative along every differentiable
input path satisfying the denominator conditions at the point. -/
theorem hasDerivAt_eval_path (ds : Fin n → RatExpr n) (e : RatExpr n)
    (x : ℝ → Fin n → ℝ) (t : ℝ)
    (hx : ∀ i,HasDerivAt (fun s => x s i) ((ds i).eval (x t)) t)
    (he : e.Valid (x t)) :
    HasDerivAt (fun s => e.eval (x s)) ((differentiate ds e).eval (x t)) t := by
  induction e with
  | const q => simpa only [eval,differentiate,Rat.cast_zero] using hasDerivAt_const t (q:ℝ)
  | var i => exact hx i
  | neg e ih => exact (ih he).neg
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)
  | mul e f ihe ihf =>
    convert (ihe he.1).mul (ihf he.2) using 1 <;>
      first | rfl | simp only [differentiate,eval,Pi.mul_apply]
  | inv e ih =>
    have hd := (ih he.1).inv he.2
    convert hd using 1 <;>
      first | rfl | simp only [differentiate,eval,pow_two,div_eq_mul_inv,neg_mul]

/-- Applying the same checked differentiation a second time gives the actual
second derivative expression, with no finite-difference approximation. -/
theorem hasDerivAt_differentiated_path (ds : Fin n → RatExpr n) (e : RatExpr n)
    (x : ℝ → Fin n → ℝ) (t : ℝ)
    (hx : ∀ i,HasDerivAt (fun s => x s i) ((ds i).eval (x t)) t)
    (hds : ∀ i,(ds i).Valid (x t)) (he : e.Valid (x t)) :
    HasDerivAt (fun s => (differentiate ds e).eval (x s))
      ((differentiate ds (differentiate ds e)).eval (x t)) t :=
  hasDerivAt_eval_path ds (differentiate ds e) x t hx (differentiate_valid ds hds he)

def logDerivative (ds : Fin n → RatExpr n) (e : RatExpr n) : RatExpr n :=
  .mul (differentiate ds e) (.inv e)

def logSecond (ds : Fin n → RatExpr n) (e : RatExpr n) : RatExpr n :=
  differentiate ds (logDerivative ds e)

theorem logSecond_eval (ds : Fin n → RatExpr n) (e : RatExpr n) (x : Fin n → ℝ) :
    (logSecond ds e).eval x =
      (differentiate ds (differentiate ds e)).eval x/e.eval x-
        ((differentiate ds e).eval x/e.eval x)^2 := by
  simp only [logSecond,logDerivative,differentiate,eval,div_eq_mul_inv,mul_inv_rev]
  ring

theorem hasDerivAt_log_eval_path (ds : Fin n → RatExpr n) (e : RatExpr n)
    (x : ℝ → Fin n → ℝ) (t : ℝ)
    (hx : ∀ i,HasDerivAt (fun s => x s i) ((ds i).eval (x t)) t)
    (he : e.Valid (x t)) (hne : e.eval (x t)≠0) :
    HasDerivAt (fun s => Real.log (e.eval (x s))) ((logDerivative ds e).eval (x t)) t := by
  simpa only [logDerivative,eval,div_eq_mul_inv] using
    (hasDerivAt_eval_path ds e x t hx he).log hne

theorem hasDerivAt_logDerivative_path (ds : Fin n → RatExpr n) (e : RatExpr n)
    (x : ℝ → Fin n → ℝ) (t : ℝ)
    (hx : ∀ i,HasDerivAt (fun s => x s i) ((ds i).eval (x t)) t)
    (hds : ∀ i,(ds i).Valid (x t)) (he : e.Valid (x t)) (hne : e.eval (x t)≠0) :
    HasDerivAt (fun s => (logDerivative ds e).eval (x s)) ((logSecond ds e).eval (x t)) t :=
  hasDerivAt_eval_path ds (logDerivative ds e) x t hx
    ⟨differentiate_valid ds hds he,⟨he,hne⟩⟩

end OptimalG.Certificates.RatExpr
