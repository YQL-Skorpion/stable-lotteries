import OptimalG.Certificates.ReferenceMatchedDisplacement
import OptimalG.Certificates.ReferenceRefinementField
import OptimalG.Certificates.ReferencePositionalPushforward

/-! The actual matched displacement is the cropped rank test. Refinement
preserves this identity even when an early branch has entered the central
profile. Only cap-prefix pieces are fixed. -/
namespace OptimalG.Certificates.ReferenceProfileCell
open Set

theorem frameCheck_cap_not_mem (ref : Transport.ReferenceData) (p : ReferenceProfileCell)
    (hf : p.frameCheck ref=true) (hp : p.piece.isSome=false) {r : ℝ}
    (hr : r∈Ioo (p.lo:ℝ) p.hi) : r∉Icc (ref.leftContact:ℝ) ref.rightContact := by
  have hgeom := (Bool.and_eq_true_iff.mp hf).2
  cases he : p.piece with
  | none=>
    have hh : p.lo≤p.hi ∧ p.hi≤ref.leftContact := by
      simpa only [Transport.ReferenceFlowCell.localProfileCheck,he,decide_eq_true_eq]
        using hgeom
    have hlt : r<(ref.leftContact:ℝ) := hr.2.trans_le (by exact_mod_cast hh.2)
    exact fun hm=>not_lt_of_ge hm.1 hlt
  | some piece=>simp [he] at hp

end OptimalG.Certificates.ReferenceProfileCell

namespace OptimalG.Certificates.Transport
open Set MeasureTheory
namespace ReferenceScalarCell

theorem matchedDisplacement_refinement {parent child : ReferenceScalarCell} {lo hi : ℚ}
    (hc : parent.flow.refinementCheck child.flow lo hi=true)
    (useR : Bool) (G : ℝ→ℝ) (t : ℝ) :
    child.matchedDisplacement useR G t=
      parent.matchedDisplacement useR G ((lo:ℝ)+(hi-lo)*t) := by
  have h : child.flow.lam=parent.flow.lam ∧ child.flow.slack=parent.flow.slack ∧
      child.flow.level=parent.flow.level ∧ child.flow.late=parent.flow.late ∧
      child.flow.rPiece=parent.flow.rPiece ∧ child.flow.aPiece=parent.flow.aPiece ∧
      child.flow.segment.left=parent.flow.interpolateNode lo ∧
      child.flow.segment.right=parent.flow.interpolateNode hi ∧
      0≤lo ∧ lo<hi ∧ hi≤1 := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
  have hf := ReferenceFlowCell.refinementCheck_fields hc t
  cases useR
  · simpa only [matchedDisplacement,globalMatchedRank,rankProfile,Bool.false_eq_true,if_false,aProfile,
      referenceRank,h.2.2.2.2.2.1,hf.2.1]
  · simpa only [matchedDisplacement,globalMatchedRank,rankProfile,if_true,rProfile,
      referenceRank,h.2.2.2.2.1,hf.1]

theorem referenceRank_timeParameter (c : ReferenceScalarCell) (useR : Bool) (z : ℝ) :
    c.referenceRank useR (c.flow.timeParameter z)=
      c.flow.segment.rankMap (if useR then (·.r) else (·.a)) z := by
  cases useR <;>
    simp only [referenceRank,Bool.false_eq_true,if_false,if_true,ReferenceFlowCell.rankR,ReferenceFlowCell.rankA,
      ReferenceFlowCell.affineExpr,RatExpr.evalOne,RatExpr.eval_addNotation,
      RatExpr.eval_mulNotation,RatExpr.eval,ReferenceFlowCell.timeParameter,
      ReferenceFlowCell.length,ReferenceSegment.rankMap,ReferenceSegment.slope,
      Rat.cast_sub,Rat.cast_div] <;> ring

theorem matchedDisplacement_eq_cropped (c : ReferenceScalarCell) (useR : Bool)
    (G : ℝ→ℝ) {a b t : ℝ}
    (hcentral : (c.rankProfile useR ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).piece.isSome=true →
      c.referenceRank useR t∈Icc a b)
    (hcap : (c.rankProfile useR ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).piece.isSome=false →
      c.referenceRank useR t∉Icc a b) :
    c.matchedDisplacement useR G t=
      (Icc a b).indicator (fun r=>G r-r) (c.referenceRank useR t) := by
  unfold matchedDisplacement globalMatchedRank
  split_ifs with hp
  · exact (indicator_of_mem (hcentral hp) _).symm
  · have hfalse : (c.rankProfile useR ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).piece.isSome=false :=
      Bool.eq_false_iff.mpr hp
    rw [indicator_of_notMem (hcap hfalse),sub_self]

theorem matchedDisplacement_timeParameter_cropped (c : ReferenceScalarCell)
    (ref : ReferenceData) (useR : Bool) (G : ℝ→ℝ)
    (hframe : (c.rankProfile useR ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).frameCheck ref=true)
    (ht : (c.flow.segment.left.z:ℝ)<c.flow.segment.right.z)
    (hr : (((if useR then (·.r) else (·.a)) c.flow.segment.left):ℝ)<
      ((if useR then (·.r) else (·.a)) c.flow.segment.right:ℚ))
    {z : ℝ} (hz : z∈Ioo (c.flow.segment.left.z:ℝ) c.flow.segment.right.z) :
    c.matchedDisplacement useR G (c.flow.timeParameter z)=
      (Icc (ref.leftContact:ℝ) ref.rightContact).indicator (fun r=>G r-r)
        (c.flow.segment.rankMap (if useR then (·.r) else (·.a)) z) := by
  have hri := c.flow.segment.rankMap_mem_Ioo_real (if useR then (·.r) else (·.a)) ht
    (by cases useR <;> simpa using hr) hz
  have he := c.referenceRank_timeParameter useR z
  rw [←he]
  apply c.matchedDisplacement_eq_cropped useR G
  · intro hp
    apply ReferenceProfileCell.frameCheck_central_mem ref _ hframe hp
    rw [he]
    cases useR <;>
      simpa [rankProfile,rProfile,aProfile] using
        And.intro hri.1.le hri.2.le
  · intro hp
    apply ReferenceProfileCell.frameCheck_cap_not_mem ref _ hframe hp
    rw [he]
    cases useR <;>
      simpa [rankProfile,rProfile,aProfile] using hri

end ReferenceScalarCell

theorem referenceDisplacement_on_refined_cell
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    (hscalar : ∀ f,(scalarFor f).flow=f)
    {start finish lo hi : ℚ} {coarse : List ReferenceFlowCell}
    {parent child : ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish coarse=true) (hm : parent∈coarse)
    (href : parent.refinementCheck child lo hi=true) (useR : Bool) (G : ℝ→ℝ) {z : ℝ}
    (hz : z∈Ioc (child.segment.left.z:ℝ) child.segment.right.z) :
    referenceDisplacement scalarFor coarse useR G z=
      (scalarFor child).matchedDisplacement useR G (child.timeParameter z) := by
  have hp := (referenceFlowCoverCheck_bounds hc hm).2.1
  have hzparent := ReferenceFlowCell.refinement_mem_parent href hp hz
  have ht := (ReferenceFlowCell.refinement_time_geometry href hp).2.2.2 z
  have href' : (scalarFor parent).flow.refinementCheck (scalarFor child).flow lo hi=true := by
    simpa only [hscalar] using href
  unfold referenceDisplacement
  rw [referenceField_on_cell _ hc hm hzparent,ht]
  exact (ReferenceScalarCell.matchedDisplacement_refinement href' useR G _).symm

/-- Local crop equality used by the checked-partition pushforward theorem.
The central/cap alternatives are just finite rank-image bounds; no condition
on the positional force or on whether the control is early is needed. -/
theorem referenceDisplacement_refined_crop
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    (hscalar : ∀ f,(scalarFor f).flow=f)
    {start finish lo hi : ℚ} {coarse : List ReferenceFlowCell}
    {parent child : ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish coarse=true) (hm : parent∈coarse)
    (href : parent.refinementCheck child lo hi=true) (useR : Bool) (G : ℝ→ℝ)
    {a b z : ℝ} (hz : z∈Ioc (child.segment.left.z:ℝ) child.segment.right.z)
    (hcentral : ((scalarFor child).rankProfile useR
      ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).piece.isSome=true →
      child.segment.rankMap (if useR then (·.r) else (·.a)) z∈Icc a b)
    (hcap : ((scalarFor child).rankProfile useR
      ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).piece.isSome=false →
      child.segment.rankMap (if useR then (·.r) else (·.a)) z∉Icc a b) :
    referenceDisplacement scalarFor coarse useR G z=
      (Icc a b).indicator (fun r=>G r-r)
        (child.segment.rankMap (if useR then (·.r) else (·.a)) z) := by
  rw [referenceDisplacement_on_refined_cell scalarFor hscalar hc hm href useR G hz]
  have he := (scalarFor child).referenceRank_timeParameter useR z
  rw [hscalar] at he
  rw [←he]
  exact (scalarFor child).matchedDisplacement_eq_cropped useR G
    (by simpa only [he] using hcentral) (by simpa only [he] using hcap)

theorem referenceDisplacement_refined_crop_of_frame
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    (hscalar : ∀ f,(scalarFor f).flow=f)
    {start finish lo hi : ℚ} {coarse : List ReferenceFlowCell}
    {parent child : ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish coarse=true) (hm : parent∈coarse)
    (href : parent.refinementCheck child lo hi=true) (ref : ReferenceData)
    (useR : Bool) (G : ℝ→ℝ)
    (hframe : ((scalarFor child).rankProfile useR
      ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).frameCheck ref=true)
    (hr : (((if useR then (·.r) else (·.a)) child.segment.left):ℝ)<
      ((if useR then (·.r) else (·.a)) child.segment.right:ℚ))
    {z : ℝ} (hz : z∈Ioo (child.segment.left.z:ℝ) child.segment.right.z) :
    referenceDisplacement scalarFor coarse useR G z=
      (Icc (ref.leftContact:ℝ) ref.rightContact).indicator (fun r=>G r-r)
        (child.segment.rankMap (if useR then (·.r) else (·.a)) z) := by
  rw [referenceDisplacement_on_refined_cell scalarFor hscalar hc hm href useR G
    ⟨hz.1,hz.2.le⟩]
  have ht : (child.segment.left.z:ℝ)<child.segment.right.z := by
    exact_mod_cast (ReferenceFlowCell.refinement_time_geometry href
      (referenceFlowCoverCheck_bounds hc hm).2.1).1
  simpa only [hscalar] using (scalarFor child).matchedDisplacement_timeParameter_cropped
    ref useR G hframe (by simpa only [hscalar] using ht)
    (by simpa only [hscalar] using hr) (by simpa only [hscalar] using hz)

end OptimalG.Certificates.Transport
