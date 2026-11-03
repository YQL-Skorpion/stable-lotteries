import OptimalG.UniversalLPEncoding

/-! Interpreting sparse rational rows against real primitive data. -/
namespace OptimalG.UniversalLP
open Finset

noncomputable def termValue (w : Variables → ℝ) (t : ℕ × ℚ) : ℝ :=
  if h : t.1 < 402 then (t.2 : ℝ) * w ⟨t.1, h⟩ else 0

noncomputable def termsValue (w : Variables → ℝ) (terms : Terms) : ℝ :=
  (terms.map (termValue w)).sum

theorem single_coeff_value (w : Variables → ℝ) (i : ℕ) (q : ℚ) :
    (∑ j : Variables, ((if i = j.val then q else 0 : ℚ) : ℝ) * w j) = termValue w (i, q) := by
  by_cases hi : i < 402
  · rw [Finset.sum_eq_single (⟨i, hi⟩ : Variables)]
    · simp [termValue, hi]
    · intro j _ hji
      have hne : i ≠ j.val := by
        intro heq
        apply hji
        exact Fin.ext heq.symm
      simp [hne]
    · simp
  · have hnone (j : Variables) : i ≠ j.val := by
      intro heq
      exact hi (heq ▸ j.isLt)
    simp [hnone, termValue, hi]

theorem coeff_value (w : Variables → ℝ) (terms : Terms) :
    (∑ j, (coeff terms j : ℝ) * w j) = termsValue w terms := by
  induction terms with
  | nil => simp [coeff, termsValue]
  | cons t ts ih =>
    have heq (j : Variables) : coeff (t :: ts) j =
        (if t.1 = j.val then t.2 else 0) + coeff ts j := by simp [coeff]
    simp_rw [heq, Rat.cast_add, add_mul]
    rw [Finset.sum_add_distrib, single_coeff_value, ih]
    simp [termsValue]

theorem rowHolds_iff_terms (tag : RowTag) (w : Variables → ℝ) :
    RowHolds tag w ↔ termsValue w (rowTerms tag) ≤ rowRhs tag := by
  unfold RowHolds rowCoeff
  rw [coeff_value]

end OptimalG.UniversalLP
