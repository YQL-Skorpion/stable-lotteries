import OptimalG.Certificates.ReferenceBranchGeometry
import OptimalG.Certificates.ReferenceRankCropCheck
import OptimalG.Certificates.ReferenceDisplacementCrop

/-! The bounded endpoint checks supply every geometric premise of the actual
three-case matched-support theorem, including the cap-prefix lower rank. -/
namespace OptimalG.Certificates.Transport.ReferenceScalarCell
open Set

structure SupportGeometry (c : ReferenceScalarCell) (cut finish : ℚ) : Prop where
  r_order : (c.flow.segment.left.r:ℝ)<c.flow.segment.right.r
  a_order : (c.flow.segment.left.a:ℝ)<c.flow.segment.right.a
  a_present : c.flow.aPiece.isSome=true
  late_r_present : c.flow.late=true→c.flow.rPiece.isSome=true
  central_r_range : c.flow.rPiece.isSome=true→
    Icc (c.flow.segment.left.r:ℝ) c.flow.segment.right.r ⊆ Icc (cut:ℝ) finish
  cap_r_range : c.flow.rPiece.isSome=false→
    Icc (c.flow.segment.left.r:ℝ) c.flow.segment.right.r ⊆ Icc Variational.pLo cut
  a_range : Icc (c.flow.segment.left.a:ℝ) c.flow.segment.right.a ⊆ Icc (cut:ℝ) finish
  early_central_order : c.flow.late=false→c.flow.rPiece.isSome=true→
    ∀ z∈Icc (c.flow.segment.left.z:ℝ) c.flow.segment.right.z,
      c.flow.segment.rankMap (·.r) z≤c.flow.segment.rankMap (·.a) z

theorem supportGeometry_of_checks {c : ReferenceScalarCell} {cut finish : ℚ}
    (hbranch : c.branchGeometryCheck cut=true)
    (hR : c.flow.rankCropCheck cut finish true=true)
    (hA : c.flow.rankCropCheck cut finish false=true)
    (hlower : (1/4:ℚ)≤c.flow.segment.left.r)
    (htime : c.flow.segment.left.z<c.flow.segment.right.z) :
    c.SupportGeometry cut finish := by
  have hh : c.flow.aPiece.isSome=true ∧
      if c.flow.late then c.flow.rPiece.isSome=true ∧
        c.flow.segment.left.a≤c.flow.segment.left.r ∧
        c.flow.segment.right.a≤c.flow.segment.right.r
      else if c.flow.rPiece.isSome then
        c.flow.segment.left.r≤c.flow.segment.left.a ∧
        c.flow.segment.right.r≤c.flow.segment.right.a
      else c.flow.rPiece=none ∧ c.flow.segment.left.r≤cut ∧ c.flow.segment.right.r≤cut :=
    of_decide_eq_true hbranch
  refine ⟨?_,?_,hh.1,?_,?_,?_,?_,?_⟩
  · exact_mod_cast ReferenceFlowCell.rankCropCheck_order hR
  · exact_mod_cast ReferenceFlowCell.rankCropCheck_order hA
  · intro hl
    have hlate : c.flow.rPiece.isSome=true ∧
        c.flow.segment.left.a≤c.flow.segment.left.r ∧
        c.flow.segment.right.a≤c.flow.segment.right.r := by
      simpa only [hl,if_true] using hh.2
    exact hlate.1
  · intro hp
    exact ReferenceFlowCell.rankCropCheck_central_image hR hp
  · intro hp
    have hc : c.flow.segment.left.r<c.flow.segment.right.r ∧
        if c.flow.rPiece.isSome then cut≤c.flow.segment.left.r ∧ c.flow.segment.right.r≤finish
          else c.flow.segment.right.r≤cut := of_decide_eq_true hR
    simp only [hp,Bool.false_eq_true,if_false] at hc
    apply Icc_subset_Icc
    · change (1/4:ℝ)≤(c.flow.segment.left.r:ℝ)
      have hh : (((1/4:ℚ)):ℝ) ≤ (c.flow.segment.left.r:ℝ) := by exact_mod_cast hlower
      norm_num at hh
      exact hh
    · exact_mod_cast hc.2
  · exact ReferenceFlowCell.rankCropCheck_central_image hA hh.1
  · intro hl hp z hz
    have he : c.flow.segment.left.r≤c.flow.segment.left.a ∧
        c.flow.segment.right.r≤c.flow.segment.right.a := by
      simpa only [hl,hp,Bool.false_eq_true,if_false,if_true] using hh.2
    have h := ReferenceFlowCell.affineExpr_le_of_endpoints he.1 he.2
      (c.flow.timeParameter_mem htime hz)
    change c.referenceRank true (c.flow.timeParameter z) ≤
      c.referenceRank false (c.flow.timeParameter z) at h
    simpa only [referenceRank_timeParameter, Bool.false_eq_true, if_true, if_false] using h


end OptimalG.Certificates.Transport.ReferenceScalarCell
