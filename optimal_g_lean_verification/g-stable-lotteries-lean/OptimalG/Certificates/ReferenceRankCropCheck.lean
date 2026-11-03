import OptimalG.Certificates.ReferenceFlowGeometry

/-! Exact endpoint checks decide whether an affine reference rank lies in
the matching interval or strictly before it. The open time cells exclude
only finitely many joins; no positional force is discarded at a branch. -/
namespace OptimalG.Certificates.Transport
open Set
namespace ReferenceSegment

theorem rankMap_mem_Ioo {seg : ReferenceSegment} {rank : ReferenceNode→ℚ}
    (ht : seg.left.z<seg.right.z) (hr : rank seg.left<rank seg.right)
    {z : ℝ} (hz : z∈Ioo (seg.left.z:ℝ) seg.right.z) :
    seg.rankMap rank z∈Ioo (rank seg.left:ℝ) (rank seg.right:ℝ) := by
  have ht' : (seg.left.z:ℝ)<seg.right.z := by exact_mod_cast ht
  have hp : 0<(seg.slope rank:ℝ) := by
    exact_mod_cast (div_pos (sub_pos.mpr hr) (sub_pos.mpr ht) : 0<seg.slope rank)
  have he : (rank seg.right:ℝ)=(rank seg.left:ℝ)+(seg.slope rank:ℝ)*
      ((seg.right.z:ℝ)-seg.left.z) := by
    simp only [slope,Rat.cast_div,Rat.cast_sub]
    field_simp [sub_ne_zero.mpr ht'.ne']
    <;> ring
  have h1 := mul_pos hp (sub_pos.mpr hz.1)
  have h2 := mul_lt_mul_of_pos_left (sub_lt_sub_right hz.2 (seg.left.z:ℝ)) hp
  unfold rankMap
  constructor <;> linarith

end ReferenceSegment
namespace ReferenceFlowCell

def rankCropCheck (left right : ℚ) (useR : Bool) (c : ReferenceFlowCell) : Bool :=
  let rank : ReferenceNode→ℚ := if useR then (·.r) else (·.a)
  let central := if useR then c.rPiece.isSome else c.aPiece.isSome
  decide (rank c.segment.left<rank c.segment.right ∧
    if central then left≤rank c.segment.left ∧ rank c.segment.right≤right
    else rank c.segment.right≤left)

theorem rankCropCheck_order {left right : ℚ} {useR : Bool} {c : ReferenceFlowCell}
    (hc : c.rankCropCheck left right useR=true) :
    (if useR then c.segment.left.r else c.segment.left.a)<
      (if useR then c.segment.right.r else c.segment.right.a) := by
  have hh := of_decide_eq_true hc
  cases useR <;> simpa using hh.1

theorem rankCropCheck_region {left right : ℚ} {useR : Bool} {c : ReferenceFlowCell}
    (hc : c.rankCropCheck left right useR=true)
    (ht : c.segment.left.z<c.segment.right.z) {z : ℝ}
    (hz : z∈Ioo (c.segment.left.z:ℝ) c.segment.right.z) :
    let r := c.segment.rankMap (if useR then (·.r) else (·.a)) z
    if (if useR then c.rPiece.isSome else c.aPiece.isSome) then
      r∈Icc (left:ℝ) right else r∉Icc (left:ℝ) right := by
  let rank : ReferenceNode→ℚ := if useR then (·.r) else (·.a)
  have hh : rank c.segment.left<rank c.segment.right ∧
      if (if useR then c.rPiece.isSome else c.aPiece.isSome) then
        left≤rank c.segment.left ∧ rank c.segment.right≤right
      else rank c.segment.right≤left := of_decide_eq_true hc
  have hr := ReferenceSegment.rankMap_mem_Ioo ht hh.1 hz
  dsimp only
  by_cases hcentral : (if useR then c.rPiece.isSome else c.aPiece.isSome) = true
  · rw [if_pos hcentral] at hh ⊢
    exact ⟨(show (left:ℝ)≤rank c.segment.left by exact_mod_cast hh.2.1).trans hr.1.le,
      hr.2.le.trans (by exact_mod_cast hh.2.2)⟩
  · rw [if_neg hcentral] at hh ⊢
    have hl : (rank c.segment.right:ℝ)≤left := by exact_mod_cast hh.2
    exact fun hm=>(not_lt_of_ge hm.1) (hr.2.trans_le hl)

theorem rankCropCheck_central_image {left right : ℚ} {useR : Bool} {c : ReferenceFlowCell}
    (hc : c.rankCropCheck left right useR=true)
    (hcentral : (if useR then c.rPiece.isSome else c.aPiece.isSome)=true) :
    Icc (((if useR then (·.r) else (·.a)) c.segment.left):ℝ)
      (((if useR then (·.r) else (·.a)) c.segment.right):ℝ) ⊆ Icc (left:ℝ) right := by
  let rank : ReferenceNode→ℚ := if useR then (·.r) else (·.a)
  have hh : rank c.segment.left<rank c.segment.right ∧
      if (if useR then c.rPiece.isSome else c.aPiece.isSome) then
        left≤rank c.segment.left ∧ rank c.segment.right≤right
      else rank c.segment.right≤left := of_decide_eq_true hc
  rw [if_pos hcentral] at hh
  have hsub : Icc (rank c.segment.left : ℝ) (rank c.segment.right : ℝ) ⊆
      Icc (left : ℝ) right :=
    Icc_subset_Icc (by exact_mod_cast hh.2.1) (by exact_mod_cast hh.2.2)
  cases useR <;> simpa [rank] using hsub

end ReferenceFlowCell
end OptimalG.Certificates.Transport
