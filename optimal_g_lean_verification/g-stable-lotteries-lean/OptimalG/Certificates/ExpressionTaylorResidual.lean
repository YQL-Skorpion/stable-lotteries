import OptimalG.Certificates.ExpressionHessian
import OptimalG.Certificates.IntegerValidity
import OptimalG.Certificates.IntegerBoxes
import OptimalG.VariationalTransportTaylor

/-! A midpoint Taylor certificate for a rational expression on the unit
interval. It is intended to validate small ODE residuals without interval
dependency from subtracting almost equal functions over a whole cell. -/
namespace OptimalG.Certificates
open Set

theorem second_order_from_midpoint_lower {f f' f'' : ℝ→ℝ} {B t : ℝ}
    (hf : ∀ u∈Icc (0:ℝ) 1,HasDerivAt f (f' u) u)
    (hf' : ∀ u∈Icc (0:ℝ) 1,HasDerivAt f' (f'' u) u)
    (hsecond : ∀ u∈Icc (0:ℝ) 1,-B≤f'' u) (ht : t∈Icc (0:ℝ) 1) :
    f (1/2)+f' (1/2)*(t-1/2)-B*(t-1/2)^2/2≤f t := by
  let path : ℝ→ℝ := fun u => 1/2+(t-1/2)*u
  have hpath (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : path u∈Icc (0:ℝ) 1 := by
    have h := (convex_Icc (0:ℝ) 1) (by norm_num : (1/2:ℝ)∈Icc 0 1) ht
      (show 0≤1-u by linarith [hu.2]) hu.1 (by ring : 1-u+u=1)
    convert h using 1 <;> simp only [path,smul_eq_mul] <;> ring
  have hd (u : ℝ) : HasDerivAt path (t-1/2) u := by
    convert! ((hasDerivAt_id u).const_mul (t-1/2)).const_add (1/2) using 1 <;>
      first | rfl | simp [path]
  have h := Variational.segment_second_order_lower
    (f := fun u => f (path u)) (f' := fun u => f' (path u)*(t-1/2))
    (f'' := fun u => f'' (path u)*(t-1/2)^2) (c := -B*(t-1/2)^2)
    (fun u hu => (hf (path u) (hpath u hu)).comp u (hd u))
    (fun u hu => by
      convert ((hf' (path u) (hpath u hu)).comp u (hd u)).mul_const (t-1/2) using 1 <;>
        first | rfl | ring)
    (fun u hu => mul_le_mul_of_nonneg_right (hsecond (path u) (hpath u ⟨hu.1.le,hu.2.le⟩))
      (sq_nonneg (t-1/2)))
  have he : (1/2:ℝ)+(t-1/2)=t := by ring
  simp only [path,mul_zero,add_zero,mul_one] at h
  rw [he] at h
  simpa only [sub_eq_add_neg,neg_mul,neg_div] using h

theorem midpoint_second_order_abs_bound {f f' f'' : ℝ→ℝ} {B0 B1 B2 t : ℝ}
    (hf : ∀ u∈Icc (0:ℝ) 1,HasDerivAt f (f' u) u)
    (hf' : ∀ u∈Icc (0:ℝ) 1,HasDerivAt f' (f'' u) u)
    (h0 : |f (1/2)|≤B0) (h1 : |f' (1/2)|≤B1)
    (h2 : ∀ u∈Icc (0:ℝ) 1,|f'' u|≤B2) (ht : t∈Icc (0:ℝ) 1) :
    |f t|≤B0+B1/2+B2/8 := by
  have hB1 : 0≤B1 := (abs_nonneg _).trans h1
  have hB2 : 0≤B2 := (abs_nonneg _).trans (h2 (1/2) (by norm_num))
  have hlo := second_order_from_midpoint_lower hf hf'
    (fun u hu => (abs_le.mp (h2 u hu)).1) ht
  have hhi := second_order_from_midpoint_lower
    (fun u hu => (hf u hu).neg) (fun u hu => (hf' u hu).neg)
    (fun u hu => show -B2≤ -f'' u by linarith [(abs_le.mp (h2 u hu)).2]) ht
  have hd : |t-1/2|≤(1/2:ℝ) := abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hp : |f' (1/2)*(t-1/2)|≤B1/2 := by
    rw [abs_mul]
    nlinarith only [mul_le_mul h1 hd (abs_nonneg _) hB1]
  have hs : (t-1/2)^2≤(1/4:ℝ) := by
    nlinarith [mul_nonneg ht.1 (show 0≤1-t by linarith [ht.2])]
  have hq := mul_le_mul_of_nonneg_left hs hB2
  have h0' := abs_le.mp h0
  have hp' := abs_le.mp hp
  apply abs_le.mpr
  constructor <;> dsimp at hhi <;> linarith

namespace IntegerInterval

def maxAbs (a : IntegerInterval) : ℤ := max |a.lo| |a.hi|

theorem maxAbs_nonneg (a : IntegerInterval) : 0≤a.maxAbs :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem abs_bound {s : ℕ} (hs : 0<s) {a : IntegerInterval} {x : ℝ}
    (hx : a.Contains s x) : |x|≤(a.maxAbs:ℝ)/(s:ℝ) := by
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  have hl : -(a.maxAbs:ℝ)≤a.lo := by
    exact_mod_cast (show -a.maxAbs≤a.lo by
      have h := (neg_abs_le a.lo)
      have hh := le_max_left |a.lo| |a.hi|
      dsimp [maxAbs]
      linarith)
  have hu : (a.hi:ℝ)≤a.maxAbs := by
    exact_mod_cast (le_abs_self a.hi).trans (le_max_right |a.lo| |a.hi|)
  apply abs_le.mpr
  constructor
  · rw [←neg_div]
    exact (div_le_div_of_nonneg_right hl hs'.le).trans (lower_bound hs hx)
  · exact (upper_bound hs hx).trans (div_le_div_of_nonneg_right hu hs'.le)

end IntegerInterval
namespace RatExpr

theorem differentiate_valid_base {n : ℕ} (ds : Fin n→RatExpr n) {e : RatExpr n}
    {x : Fin n→ℝ} (h : (differentiate ds e).Valid x) : e.Valid x := by
  induction e with
  | const q => trivial
  | var i => trivial
  | neg e ih => exact ih h
  | add e f ihe ihf => exact ⟨ihe h.1,ihf h.2⟩
  | mul e f ihe ihf => exact ⟨h.2.1,h.1.2⟩
  | inv e ih =>
    refine ⟨h.2.1.1,?_⟩
    intro he
    apply h.2.2
    simp only [eval,he,mul_zero]

theorem partial_valid_base {n : ℕ} {e : RatExpr n} {x : Fin n→ℝ} (i : Fin n)
    (h : (partialExpr i e).Valid x) : e.Valid x := differentiate_valid_base (basis i) h

noncomputable def evalOne (e : RatExpr 1) (t : ℝ) : ℝ := e.eval (fun _ => t)

theorem evalOne_hasDerivAt (e : RatExpr 1) (t : ℝ) (h : e.Valid (fun _ => t)) :
    HasDerivAt e.evalOne ((partialExpr 0 e).evalOne t) t := by
  have hd := hasDerivAt_eval_gradient e (fun u _ => u) (fun _ => 1) t
    (fun _ => hasDerivAt_id t) h
  convert! hd using 1 <;> first | rfl |
    simp only [evalOne,Fin.sum_univ_succ,Fin.sum_univ_zero,mul_one,add_zero]

def midpointTaylorCheck (s : ℕ) (e : RatExpr 1) (bound : ℤ) : Bool :=
  let mid : Fin 1→IntegerInterval := fun _ => IntegerInterval.pointRounded s (1/2)
  let unit : Fin 1→IntegerInterval := fun _ => IntegerInterval.fromRat s ⟨0,1⟩
  match e.integerInterval s mid,(partialExpr 0 e).integerInterval s mid,
      (partialExpr 0 (partialExpr 0 e)).integerInterval s unit with
  | some b0,some b1,some b2 => decide (8*b0.maxAbs+4*b1.maxAbs+b2.maxAbs≤8*bound)
  | _,_,_ => false

/-- Every reciprocal and every derivative in this residual bound is checked
by the same exact integer arithmetic on the full unit interval. -/
theorem midpointTaylorCheck_sound {s : ℕ} (hs : 0<s) (e : RatExpr 1) (bound : ℤ)
    (hc : e.midpointTaylorCheck s bound=true) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    |e.evalOne t|≤(bound:ℝ)/(s:ℝ) := by
  let mid : Fin 1→IntegerInterval := fun _ => IntegerInterval.pointRounded s (1/2)
  let unit : Fin 1→IntegerInterval := fun _ => IntegerInterval.fromRat s ⟨0,1⟩
  have hm : ∀ i,(mid i).Contains s (1/2:ℝ) := by
    intro i
    simpa [mid] using IntegerInterval.pointRounded_contains s (1/2)
  have hu (u : ℝ) (h : u∈Icc (0:ℝ) 1) : ∀ i,(unit i).Contains s u := by
    intro i
    apply IntegerInterval.fromRat_contains hs
    simpa [RatInterval.Contains] using h
  change (match e.integerInterval s mid,(partialExpr 0 e).integerInterval s mid,
      (partialExpr 0 (partialExpr 0 e)).integerInterval s unit with
    | some b0,some b1,some b2 => decide (8*b0.maxAbs+4*b1.maxAbs+b2.maxAbs≤8*bound)
    | _,_,_ => false)=true at hc
  cases h0 : e.integerInterval s mid with
  | none => simp only [h0,Bool.false_eq_true] at hc
  | some b0 =>
    cases h1 : (partialExpr 0 e).integerInterval s mid with
    | none => simp only [h0,h1,Bool.false_eq_true] at hc
    | some b1 =>
      cases h2 : (partialExpr 0 (partialExpr 0 e)).integerInterval s unit with
      | none => simp only [h0,h1,h2,Bool.false_eq_true] at hc
      | some b2 =>
        have hvalid (u : ℝ) (hu' : u∈Icc (0:ℝ) 1) :
            (partialExpr 0 e).Valid (fun _ => u) :=
          partial_valid_base 0 (integerInterval_valid hs unit (fun _ => u) (hu u hu') _ h2)
        have h := midpoint_second_order_abs_bound
          (fun u hu' => evalOne_hasDerivAt e u (partial_valid_base 0 (hvalid u hu')))
          (fun u hu' => evalOne_hasDerivAt (partialExpr 0 e) u (hvalid u hu'))
          (IntegerInterval.abs_bound hs (integerInterval_sound hs mid (fun _ => 1/2) hm e h0))
          (IntegerInterval.abs_bound hs (integerInterval_sound hs mid (fun _ => 1/2) hm _ h1))
          (fun u hu' => IntegerInterval.abs_bound hs
            (integerInterval_sound hs unit (fun _ => u) (hu u hu') _ h2)) ht
        have hn : 8*b0.maxAbs+4*b1.maxAbs+b2.maxAbs≤8*bound := by
          simpa only [h0,h1,h2,decide_eq_true_eq] using hc
        have hn' : 8*(b0.maxAbs:ℝ)+4*(b1.maxAbs:ℝ)+(b2.maxAbs:ℝ)≤8*(bound:ℝ) := by
          exact_mod_cast hn
        have hs' : (0:ℝ)<s := by exact_mod_cast hs
        have hsum : (b0.maxAbs:ℝ)/s+((b1.maxAbs:ℝ)/s)/2+((b2.maxAbs:ℝ)/s)/8≤
            (bound:ℝ)/s := by
          apply (le_div_iff₀ hs').mpr
          field_simp
          linarith
        exact h.trans hsum

end RatExpr
end OptimalG.Certificates
