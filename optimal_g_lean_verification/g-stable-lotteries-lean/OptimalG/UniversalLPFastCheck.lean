import OptimalG.UniversalLPCheck

/-! A sparse, kernel-checkable implementation of the dual residual test.
The row products are formed once, and their coefficients are combined before
comparison with the proposed residual.  The final theorem recovers the original
checker exactly, so all existing semantic theorems apply unchanged. -/
namespace OptimalG.UniversalLP

/-- Insert one sparse term into an index-sorted list, combining equal indices
and deleting zero coefficients.  Coefficient preservation does not require the
input list to be sorted. -/
def insertTerm (t : ℕ × ℚ) : Terms → Terms
  | [] => if t.2 = 0 then [] else [t]
  | a :: ts =>
      if t.2 = 0 then a :: ts
      else if t.1 < a.1 then t :: a :: ts
      else if t.1 = a.1 then
        if t.2 + a.2 = 0 then ts else (t.1, t.2 + a.2) :: ts
      else a :: insertTerm t ts

/-- Canonical sparse normalization, computed using exact rational arithmetic. -/
def normalizeTerms (ts : Terms) : Terms := ts.foldr insertTerm []

def scaleTerms (c : ℚ) (ts : Terms) : Terms := ts.map fun t => (t.1, c * t.2)

@[simp] theorem coeff_nil (j : Variables) : coeff [] j = 0 := by simp [coeff]
@[simp] theorem coeff_cons (t : ℕ × ℚ) (ts : Terms) (j : Variables) :
    coeff (t :: ts) j = (if t.1 = j.val then t.2 else 0) + coeff ts j := by
  simp [coeff]

@[simp] theorem coeff_append (a b : Terms) (j : Variables) :
    coeff (a ++ b) j = coeff a j + coeff b j := by simp [coeff]

@[simp] theorem coeff_insertTerm (t : ℕ × ℚ) (ts : Terms) (j : Variables) :
    coeff (insertTerm t ts) j = (if t.1 = j.val then t.2 else 0) + coeff ts j := by
  induction ts with
  | nil =>
      by_cases ht : t.2 = 0 <;> simp [insertTerm, ht]
  | cons a ts ih =>
      simp only [insertTerm]
      by_cases ht : t.2 = 0
      · simp [ht]
      rw [if_neg ht]
      by_cases hlt : t.1 < a.1
      · rw [if_pos hlt]
        simp only [coeff_cons]
      rw [if_neg hlt]
      by_cases heq : t.1 = a.1
      · rw [if_pos heq]
        by_cases hzero : t.2 + a.2 = 0
        · rw [if_pos hzero]
          by_cases hj : a.1 = j.val
          · simp only [coeff_cons, heq, hj, if_true]
            linarith
          · simp [heq, hj]
        · rw [if_neg hzero]
          by_cases hj : a.1 = j.val <;> simp [heq, hj] <;> ring
      · rw [if_neg heq]
        simp only [coeff_cons, ih]
        ring

@[simp] theorem coeff_normalizeTerms (ts : Terms) (j : Variables) :
    coeff (normalizeTerms ts) j = coeff ts j := by
  induction ts with
  | nil => simp [normalizeTerms]
  | cons t ts ih =>
      simp only [normalizeTerms, List.foldr_cons, coeff_insertTerm, coeff_cons]
      exact congrArg ((if t.1 = j.val then t.2 else 0) + ·) ih

@[simp] theorem coeff_scaleTerms (c : ℚ) (ts : Terms) (j : Variables) :
    coeff (scaleTerms c ts) j = c * coeff ts j := by
  induction ts with
  | nil => simp [scaleTerms]
  | cons t ts ih =>
      simp only [scaleTerms, List.map_cons, coeff_cons] at *
      rw [ih]
      by_cases h : t.1 = j.val <;> simp [h, mul_add]

theorem coeff_flatten (tss : List Terms) (j : Variables) :
    coeff tss.flatten j = (tss.map fun ts => coeff ts j).sum := by
  induction tss with
  | nil => simp
  | cons ts tss ih => simp [ih]

namespace DualProposal

/-- Expand all weighted rows just once, with the signs of the residual
`objective - weighted rows`. -/
def expandedResidual (d : DualProposal) (terms : Array Terms) : Terms :=
  d.objective ++ (List.ofFn fun i : Fin d.support.size =>
    scaleTerms (-d.multiplier i) (terms[d.rowIndex i]!)).flatten

theorem coeff_expandedResidual (d : DualProposal) (terms : Array Terms) (j : Variables) :
    coeff (d.expandedResidual terms) j =
      coeff d.objective j - ∑ i, d.multiplier i * d.cachedMatrix terms i j := by
  simp only [expandedResidual, coeff_append, coeff_flatten, List.map_ofFn,
    Function.comp_def, coeff_scaleTerms, List.sum_ofFn, neg_mul, Finset.sum_neg_distrib,
    cachedMatrix]
  ring

/-- The sparse proposed cache is checked against the computed normalization.
The remaining tests are exactly the index, sign, residual, and bound conditions
of `checkCached`. -/
def fastCheck (d : DualProposal) (rows : Array RowTag) (terms : Array Terms)
    (rhs : Array ℚ) (known : ℕ) (proposedResidual : Terms) : Bool :=
  decide (known ≤ rows.size ∧ ∀ i, d.rowIndex i < known) &&
  decide ((∀ i, d.multiplier i ≤ 0) ∧
    normalizeTerms (d.expandedResidual terms) = proposedResidual ∧
    (∀ j, coeff proposedResidual j = d.remainder j) ∧
    d.bound ≤ (∑ i, d.multiplier i * d.cachedRhs rhs i) +
      ∑ j, min (d.remainder j * lower j) (d.remainder j * upper j))

/-- A successful sparse check proves success of the original checker. -/
theorem checkCached_of_fastCheck {d : DualProposal} {rows : Array RowTag}
    {terms : Array Terms} {rhs : Array ℚ} {known : ℕ} {proposedResidual : Terms}
    (hc : d.fastCheck rows terms rhs known proposedResidual = true) :
    d.checkCached rows terms rhs known = true := by
  have hs := Bool.and_eq_true_iff.mp hc
  have hh := of_decide_eq_true hs.2
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hs.1, ?_⟩
  apply decide_eq_true
  refine ⟨hh.1, ?_, hh.2.2.2⟩
  intro j
  have he := congrArg (fun ts => coeff ts j) hh.2.1
  rw [coeff_normalizeTerms, coeff_expandedResidual, hh.2.2.1 j] at he
  linarith

/-- Direct semantic soundness, including the separately checked row cache. -/
theorem fastCheck_sound {d : DualProposal} {rows : Array RowTag}
    {terms : Array Terms} {rhs : Array ℚ} {known : ℕ} {proposedResidual : Terms}
    (hcache : checkRowCache rows terms rhs = true)
    (hc : d.fastCheck rows terms rhs known proposedResidual = true) (w : Variables → ℝ)
    (hknown : ∀ i < known, RowHolds rows[i]! w)
    (hlo : ∀ j, (lower j : ℝ) ≤ w j) (hhi : ∀ j, w j ≤ upper j) :
    (d.bound : ℝ) ≤ ∑ j, (coeff d.objective j : ℝ) * w j :=
  checkCached_sound hcache (checkCached_of_fastCheck hc) w hknown hlo hhi

end DualProposal
end OptimalG.UniversalLP
