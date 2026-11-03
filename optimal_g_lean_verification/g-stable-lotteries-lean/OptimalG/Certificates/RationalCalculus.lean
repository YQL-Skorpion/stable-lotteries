import OptimalG.Certificates.RationalPolynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Exact rational evaluation and differentiation of the checked polynomial
representation. These lemmas connect generated reference gauges to calculus. -/
namespace OptimalG.Certificates.RationalPolynomial

def evalQ : RationalPolynomial → ℚ → ℚ
  | [], _ => 0
  | c::cs, t => c+t*evalQ cs t

@[simp] theorem cast_evalQ (p : RationalPolynomial) (t : ℚ) :
    (p.evalQ t:ℝ)=p.eval (t:ℝ) := by
  induction p with
  | nil => simp [evalQ,eval]
  | cons c cs ih => simp [evalQ,eval,ih]

/-- Horner differentiation avoids requiring a polynomial library conversion. -/
def derivative : RationalPolynomial → RationalPolynomial
  | [] => []
  | _::cs => add cs (0::derivative cs)

theorem hasDerivAt_eval (p : RationalPolynomial) (t : ℝ) :
    HasDerivAt (fun x => p.eval x) (p.derivative.eval t) t := by
  induction p with
  | nil => simpa only [eval,derivative] using hasDerivAt_const t (0:ℝ)
  | cons c cs ih =>
    have hd := ((hasDerivAt_id t).mul ih).const_add (c:ℝ)
    simpa only [derivative,eval_add,eval,Rat.cast_zero,zero_add,one_mul,id_eq,Pi.mul_apply] using hd

theorem continuous_eval (p : RationalPolynomial) : Continuous (fun t:ℝ => p.eval t) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_eval p t).continuousAt

/-- A checked exact derivative identity gives the derivative after an affine
rank rescaling. Both the data and the calculus statement use the actual
polynomial expressions. -/
theorem hasDerivAt_affine_of_check {p q : RationalPolynomial} {h : ℚ}
    (hc : eqCheck p.derivative (scale h q)=true) (hh : h≠0) (a t : ℝ) :
    HasDerivAt (fun r:ℝ => p.eval ((r-a)/(h:ℝ))) (q.eval ((t-a)/(h:ℝ))) t := by
  have hd := (hasDerivAt_eval p ((t-a)/(h:ℝ))).comp t
    (((hasDerivAt_id t).sub_const a).div_const (h:ℝ))
  have he := eqCheck_sound hc ((t-a)/(h:ℝ))
  rw [eval_scale] at he
  have hh' : (h:ℝ)≠0 := by exact_mod_cast hh
  have hv : p.derivative.eval ((t-a)/(h:ℝ))*(1/(h:ℝ))=q.eval ((t-a)/(h:ℝ)) := by
    rw [he]
    field_simp
  simpa only [Function.comp_def,id_eq,hv] using hd

end OptimalG.Certificates.RationalPolynomial
