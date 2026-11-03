import OptimalG.Certificates.DifferentiableExpression
import OptimalG.Certificates.ExpressionAlgebra
import Mathlib.Analysis.Calculus.Deriv.Add

/-! Actual first and second derivatives of reified expressions, with a finite
coordinate Hessian. Mixed entries are symmetrized algebraically, so the
quadratic-form theorem does not need a separate equality-of-mixed-partials
assumption. -/
namespace OptimalG.Certificates.RatExpr
open scoped BigOperators
variable {n : ℕ}

def basis (i j : Fin n) : RatExpr n := if j=i then .const 1 else .const 0
def partialExpr (i : Fin n) (e : RatExpr n) : RatExpr n := differentiate (basis i) e

theorem basis_valid (i j : Fin n) (x : Fin n→ℝ) : (basis i j).Valid x := by
  unfold basis
  split <;> trivial

theorem partial_valid {e : RatExpr n} {x : Fin n→ℝ} (he : e.Valid x) (i : Fin n) :
    (partialExpr i e).Valid x := differentiate_valid (basis i) (fun j => basis_valid i j x) he

@[simp] theorem partial_const_eval (i : Fin n) (q : ℚ) (x : Fin n→ℝ) :
    (partialExpr i (.const q)).eval x=0 := by simp [partialExpr,differentiate,eval]
@[simp] theorem partial_var_eval (i j : Fin n) (x : Fin n→ℝ) :
    (partialExpr i (.var j)).eval x=if j=i then 1 else 0 := by
  by_cases hji : j=i <;> simp [partialExpr,differentiate,basis,eval,hji]
@[simp] theorem partial_neg_eval (i : Fin n) (e : RatExpr n) (x : Fin n→ℝ) :
    (partialExpr i (.neg e)).eval x= -(partialExpr i e).eval x := rfl
@[simp] theorem partial_add_eval (i : Fin n) (e f : RatExpr n) (x : Fin n→ℝ) :
    (partialExpr i (.add e f)).eval x=(partialExpr i e).eval x+(partialExpr i f).eval x := rfl
@[simp] theorem partial_mul_eval (i : Fin n) (e f : RatExpr n) (x : Fin n→ℝ) :
    (partialExpr i (.mul e f)).eval x=(partialExpr i e).eval x*f.eval x+e.eval x*(partialExpr i f).eval x := rfl
@[simp] theorem partial_inv_eval (i : Fin n) (e : RatExpr n) (x : Fin n→ℝ) :
    (partialExpr i (.inv e)).eval x= -((partialExpr i e).eval x/(e.eval x)^2) := by
  simp [partialExpr,differentiate,eval,pow_two,div_eq_mul_inv]

/-- The gradient expression gives the true derivative along a path with any
real coordinate velocities, not only rational directions. -/
theorem hasDerivAt_eval_gradient (e : RatExpr n) (x : ℝ→Fin n→ℝ) (v : Fin n→ℝ)
    (t : ℝ) (hx : ∀ i,HasDerivAt (fun u => x u i) (v i) t) (he : e.Valid (x t)) :
    HasDerivAt (fun u => e.eval (x u)) (∑ i,(partialExpr i e).eval (x t)*v i) t := by
  induction e with
  | const q =>
    convert! hasDerivAt_const t (q:ℝ) using 1 <;> simp [eval]
  | var j =>
    convert! hx j using 1 <;> simp [eval,Finset.sum_ite_eq']
  | neg e ih =>
    convert (ih he).neg using 1 <;> first | rfl | simp [Finset.sum_neg_distrib]
  | add e f ihe ihf =>
    convert (ihe he.1).add (ihf he.2) using 1 <;>
      first | rfl | simp [add_mul,Finset.sum_add_distrib]
  | mul e f ihe ihf =>
    have hsum : (∑ i,((partialExpr i e).eval (x t)*f.eval (x t)+
          e.eval (x t)*(partialExpr i f).eval (x t))*v i)=
        (∑ i,(partialExpr i e).eval (x t)*v i)*f.eval (x t)+
          e.eval (x t)*(∑ i,(partialExpr i f).eval (x t)*v i) := by
      calc
        _=(∑ i,((partialExpr i e).eval (x t)*v i)*f.eval (x t))+
          ∑ i,e.eval (x t)*((partialExpr i f).eval (x t)*v i) := by
            rw [←Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring
        _=_ := by rw [Finset.sum_mul,Finset.mul_sum]
    convert (ihe he.1).mul (ihf he.2) using 1 <;>
      first | rfl | simpa only [partial_mul_eval] using hsum
  | inv e ih =>
    have hsum : (∑ i,-((partialExpr i e).eval (x t)/(e.eval (x t))^2)*v i)=
        -(∑ i,(partialExpr i e).eval (x t)*v i)/(e.eval (x t))^2 := by
      calc
        _=(∑ i,(partialExpr i e).eval (x t)*v i)*(-(e.eval (x t)^2)⁻¹) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _=_ := by ring
    convert (ih he.1).inv he.2 using 1 <;>
      first | rfl | simpa only [partial_inv_eval] using hsum

def logPartial (i : Fin n) (e : RatExpr n) : RatExpr n := logDerivative (basis i) e

def logHessian (i j : Fin n) (e : RatExpr n) : RatExpr n := partialExpr j (logPartial i e)

@[simp] theorem logPartial_eval (i : Fin n) (e : RatExpr n) (x : Fin n→ℝ) :
    (logPartial i e).eval x=(partialExpr i e).eval x/e.eval x := rfl

theorem logPartial_valid {e : RatExpr n} {x : Fin n→ℝ}
    (he : e.Valid x) (hne : e.eval x≠0) (i : Fin n) : (logPartial i e).Valid x :=
  ⟨partial_valid he i,⟨he,hne⟩⟩

theorem hasDerivAt_log_gradient (e : RatExpr n) (x : ℝ→Fin n→ℝ) (v : Fin n→ℝ)
    (t : ℝ) (hx : ∀ i,HasDerivAt (fun u => x u i) (v i) t)
    (he : e.Valid (x t)) (hne : e.eval (x t)≠0) :
    HasDerivAt (fun u => Real.log (e.eval (x u)))
      (∑ i,(logPartial i e).eval (x t)*v i) t := by
  have hd := (hasDerivAt_eval_gradient e x v t hx he).log hne
  apply hd.congr_deriv
  simp only [logPartial_eval,div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The finite matrix is the actual second directional derivative. -/
theorem hasDerivAt_log_hessian (e : RatExpr n) (x : ℝ→Fin n→ℝ) (v : Fin n→ℝ)
    (t : ℝ) (hx : ∀ i,HasDerivAt (fun u => x u i) (v i) t)
    (he : e.Valid (x t)) (hne : e.eval (x t)≠0) :
    HasDerivAt (fun u => ∑ i,(logPartial i e).eval (x u)*v i)
      (∑ i,∑ j,(logHessian i j e).eval (x t)*v j*v i) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hasDerivAt_eval_gradient (logPartial i e) x v t hx (logPartial_valid he hne i)).mul_const (v i)
  simpa only [logHessian,Finset.sum_mul] using hd

/-- Symmetrizing mixed entries preserves the quadratic form exactly. -/
theorem quadratic_three (H : Fin 3→Fin 3→ℝ) (v : Fin 3→ℝ) :
    (∑ i,∑ j,H i j*v j*v i)=
      H 0 0*(v 0)^2+2*((H 0 1+H 1 0)/2)*v 0*v 1+
      2*((H 0 2+H 2 0)/2)*v 0*v 2+H 1 1*(v 1)^2+
      2*((H 1 2+H 2 1)/2)*v 1*v 2+H 2 2*(v 2)^2 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num <;> ring

end OptimalG.Certificates.RatExpr
