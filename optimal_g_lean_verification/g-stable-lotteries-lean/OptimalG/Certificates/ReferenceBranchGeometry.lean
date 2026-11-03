import OptimalG.Certificates.ReferenceMatchedGlobal

/-! Finite endpoint order checks determine the actual matched control branch.
The affine reference maps preserve endpoint inequalities, and a monotone
Stieltjes matching preserves the late order. -/
namespace OptimalG.Certificates.Transport
open Set RatExpr
namespace ReferenceFlowCell

theorem affineExpr_le_of_endpoints {lo hi lo' hi' : ℚ}
    (hl : lo≤lo') (hh : hi≤hi') {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (affineExpr lo hi).evalOne t≤(affineExpr lo' hi').evalOne t := by
  have hl' : (lo:ℝ)≤lo' := by exact_mod_cast hl
  have hh' : (hi:ℝ)≤hi' := by exact_mod_cast hh
  have h0 := mul_nonneg (sub_nonneg.mpr hl') (sub_nonneg.mpr ht.2)
  have h1 := mul_nonneg (sub_nonneg.mpr hh') ht.1
  simp only [affineExpr,evalOne,eval_addNotation,eval_mulNotation,eval,Rat.cast_sub]
  nlinarith only [h0,h1]

end ReferenceFlowCell
namespace ReferenceScalarCell

def branchGeometryCheck (cut : ℚ) (c : ReferenceScalarCell) : Bool :=
  decide (c.flow.aPiece.isSome=true ∧
    if c.flow.late then c.flow.rPiece.isSome=true ∧
      c.flow.segment.left.a≤c.flow.segment.left.r ∧
      c.flow.segment.right.a≤c.flow.segment.right.r
    else if c.flow.rPiece.isSome then
      c.flow.segment.left.r≤c.flow.segment.left.a ∧
      c.flow.segment.right.r≤c.flow.segment.right.a
    else c.flow.rPiece=none ∧ c.flow.segment.left.r≤cut ∧ c.flow.segment.right.r≤cut)

theorem branchGeometryCheck_order {cut : ℚ} {c : ReferenceScalarCell}
    (hc : c.branchGeometryCheck cut=true) {G : ℝ→ℝ} (hG : Monotone G)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hA : (cut:ℝ)≤G (c.referenceRank false t)) :
    if c.flow.late then c.globalMatchedRank false G t≤c.globalMatchedRank true G t
      else c.globalMatchedRank true G t≤c.globalMatchedRank false G t := by
  have hh : c.flow.aPiece.isSome=true ∧
      if c.flow.late then c.flow.rPiece.isSome=true ∧
        c.flow.segment.left.a≤c.flow.segment.left.r ∧ c.flow.segment.right.a≤c.flow.segment.right.r
      else if c.flow.rPiece.isSome then
        c.flow.segment.left.r≤c.flow.segment.left.a ∧
        c.flow.segment.right.r≤c.flow.segment.right.a
      else c.flow.rPiece=none ∧ c.flow.segment.left.r≤cut ∧ c.flow.segment.right.r≤cut :=
    of_decide_eq_true hc
  cases hb : c.flow.late
  · simp only [hb,Bool.false_eq_true,if_false] at hh ⊢
    by_cases hr : c.flow.rPiece.isSome=true
    · rw [if_pos hr] at hh
      exact c.globalMatchedRank_early_central_order G t hG hr hh.1
        (ReferenceFlowCell.affineExpr_le_of_endpoints hh.2.1 hh.2.2 ht)
    · rw [if_neg hr] at hh
      apply c.globalMatchedRank_early_order G t cut hh.2.1 hh.1 _ hA
      have hl := ReferenceFlowCell.affineExpr_le_of_endpoints hh.2.2.1 hh.2.2.2 ht
      simpa only [referenceRank,if_true,ReferenceFlowCell.rankR,ReferenceFlowCell.affineExpr,
        evalOne,eval_addNotation,eval_mulNotation,eval,sub_self,Rat.cast_zero,zero_mul,add_zero] using hl
  · simp only [hb,if_true] at hh ⊢
    apply c.globalMatchedRank_late_order G t hG hh.2.1 hh.1
    exact ReferenceFlowCell.affineExpr_le_of_endpoints hh.2.2.1 hh.2.2.2 ht

end ReferenceScalarCell
end OptimalG.Certificates.Transport
