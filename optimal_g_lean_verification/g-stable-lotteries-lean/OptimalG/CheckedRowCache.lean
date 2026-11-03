import OptimalG.UniversalLPCheck

/-! Row-by-row checked sparse data, avoiding repeated reconstruction of the
whole numerical array in a finite universal decidability proof. -/
namespace OptimalG.UniversalLP

structure CheckedRow where
  tag : RowTag
  terms : Terms
  rhs : ℚ
  terms_eq : terms = rowTerms tag
  rhs_eq : rhs = rowRhs tag

theorem checkedRows_cache (rs : Array CheckedRow) :
    DualProposal.checkRowCache (rs.map (·.tag)) (rs.map (·.terms)) (rs.map (·.rhs)) = true := by
  unfold DualProposal.checkRowCache
  rw [decide_eq_true_eq]
  intro i
  have hi : i.val < rs.size := by simpa only [Array.size_map] using i.isLt
  rw [getElem!_pos (rs.map CheckedRow.terms) i.val (by simpa only [Array.size_map] using hi),
    getElem!_pos (rs.map CheckedRow.rhs) i.val (by simpa only [Array.size_map] using hi),
    getElem!_pos (rs.map CheckedRow.tag) i.val (by simpa only [Array.size_map] using hi)]
  simp only [Array.getElem_map]
  exact ⟨(rs[i.val]).terms_eq, (rs[i.val]).rhs_eq⟩

end OptimalG.UniversalLP
