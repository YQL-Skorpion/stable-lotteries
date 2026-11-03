import OptimalG.Certificates.ExpressionHessian

/-! Rational expressions and all their symbolic coordinate derivatives are
invariant under changes to unused coordinates. Validity is preserved as well,
so appending interval weights cannot alter any denominator condition. -/
namespace OptimalG.Certificates.RatExpr
variable {n k : ℕ}

def UsesPrefix (k : ℕ) : RatExpr n→Prop
  | .const _=>True
  | .var i=>i.val<k
  | .neg e=>e.UsesPrefix k
  | .add e f=>e.UsesPrefix k ∧ f.UsesPrefix k
  | .mul e f=>e.UsesPrefix k ∧ f.UsesPrefix k
  | .inv e=>e.UsesPrefix k

theorem prefix_eval_eq {e : RatExpr n} (he : e.UsesPrefix k) {x y : Fin n→ℝ}
    (hxy : ∀ i,i.val<k→x i=y i) : e.eval x=e.eval y := by
  induction e with
  | const q=>rfl
  | var i=>exact hxy i he
  | neg e ih=>simp only [eval,ih he]
  | add e f ihe ihf=>simp only [eval,ihe he.1,ihf he.2]
  | mul e f ihe ihf=>simp only [eval,ihe he.1,ihf he.2]
  | inv e ih=>simp only [eval,ih he]

theorem prefix_valid_iff {e : RatExpr n} (he : e.UsesPrefix k) {x y : Fin n→ℝ}
    (hxy : ∀ i,i.val<k→x i=y i) : e.Valid x↔e.Valid y := by
  induction e with
  | const q=>rfl
  | var i=>rfl
  | neg e ih=>exact ih he
  | add e f ihe ihf=>exact and_congr (ihe he.1) (ihf he.2)
  | mul e f ihe ihf=>exact and_congr (ihe he.1) (ihf he.2)
  | inv e ih=>simp only [Valid,ih he,prefix_eval_eq (e:=e) he hxy]

theorem prefix_partial {e : RatExpr n} (he : e.UsesPrefix k) (i : Fin n) :
    (partialExpr i e).UsesPrefix k := by
  induction e with
  | const q=>trivial
  | var j=>simp only [partialExpr,differentiate,basis]; split <;> trivial
  | neg e ih=>exact ih he
  | add e f ihe ihf=>exact ⟨ihe he.1,ihf he.2⟩
  | mul e f ihe ihf=>exact ⟨⟨ihe he.1,he.2⟩,⟨he.1,ihf he.2⟩⟩
  | inv e ih=>exact ⟨ih he,⟨he,he⟩⟩

theorem prefix_logPartial {e : RatExpr n} (he : e.UsesPrefix k) (i : Fin n) :
    (logPartial i e).UsesPrefix k := ⟨prefix_partial he i,he⟩

theorem prefix_logHessian {e : RatExpr n} (he : e.UsesPrefix k) (i j : Fin n) :
    (logHessian i j e).UsesPrefix k := prefix_partial (prefix_logPartial he i) j

end OptimalG.Certificates.RatExpr
