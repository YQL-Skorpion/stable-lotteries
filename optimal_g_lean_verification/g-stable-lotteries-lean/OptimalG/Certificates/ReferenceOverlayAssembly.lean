import OptimalG.Certificates.ReferenceOverlayCell
import OptimalG.Certificates.RankSegmentFrame
import OptimalG.Certificates.RankOverlayGeometry

/-! Checked overlay selectors identify each finite interval enclosure with
exactly the contributors to the full actual pushforward density. The optional
a-contributor is absent beyond its rank image; no artificial segment is added.
-/
namespace OptimalG.Certificates.Transport
open Set

theorem rankSegmentFrameCheck_endpoints {segments : List ReferenceSegment} {nodes : List ℚ}
    {rank : ReferenceNode→ℚ} (hc : rankSegmentFrameCheck segments nodes rank=true)
    {i : ℕ} (hi : i<nodes.length-1) :
    rank (rankFrameSegment segments i).left=nodes[i]?.getD 0 ∧
      rank (rankFrameSegment segments i).right=nodes[i+1]?.getD 0 := by
  obtain ⟨hlen,hcell⟩ := Bool.and_eq_true_iff.mp hc
  have hsize : nodes.length=segments.length+1 := of_decide_eq_true hlen
  have him : i<segments.length := by omega
  exact of_decide_eq_true (List.all_eq_true.mp hcell i (List.mem_range.mpr him))

namespace RankOverlayArrays

theorem pushforward_selected {d : RankOverlayArrays} {segments : List ReferenceSegment}
    (hg : d.geometryCheck=true)
    (hR : rankSegmentFrameCheck segments d.nodeR ReferenceNode.r=true)
    (hA : rankSegmentFrameCheck segments d.nodeA ReferenceNode.a=true)
    {i : ℕ} (hi : i<d.cellCount) {r : ℝ}
    (hr : r∈Ioo (d.fineNode i) (d.fineNode (i+1))) (weightR weightA : ℝ→ℝ) :
    pushforwardDensity segments ReferenceNode.r (fun _=>weightR) r+
      pushforwardDensity segments ReferenceNode.a (fun _=>weightA) r=
    segmentDensity (rankFrameSegment segments (d.rIndex i)) ReferenceNode.r weightR r+
      (d.aIndex i).elim 0 (fun j=>segmentDensity (rankFrameSegment segments j)
        ReferenceNode.a weightA r) := by
  let wR := fun j r=>weightR ((rankFrameSegment segments j).inverseRankMap ReferenceNode.r r)/
    ((rankFrameSegment segments j).slope ReferenceNode.r:ℝ)
  let wA := fun j r=>weightA ((rankFrameSegment segments j).inverseRankMap ReferenceNode.a r)/
    ((rankFrameSegment segments j).slope ReferenceNode.a:ℝ)
  rw [rankSegmentFrameCheck_density hR,rankSegmentFrameCheck_density hA]
  change Variational.rankPartitionDensity d.rCount d.rNode wR r+
    Variational.rankPartitionDensity d.aCount d.aNode wA r=_
  rw [geometryCheck_selected hg hi hr]
  have geom := geometryCheck_sound hg
  have rg := geom.2.2.2.1 i hi
  have re := rankSegmentFrameCheck_endpoints hR rg.1
  have rr : r∈Ioo
      ((rankFrameSegment segments (d.rIndex i)).left.r:ℝ)
      (rankFrameSegment segments (d.rIndex i)).right.r := by
    constructor
    · have hh : ((rankFrameSegment segments (d.rIndex i)).left.r:ℝ)=d.rNode (d.rIndex i) :=
        by simpa only [rNode] using congrArg (fun q : ℚ => (q : ℝ)) re.1
      rw [hh]
      exact rg.2.1.trans_lt hr.1
    · have hh : ((rankFrameSegment segments (d.rIndex i)).right.r:ℝ)=d.rNode (d.rIndex i+1) :=
        by simpa only [rNode] using congrArg (fun q : ℚ => (q : ℝ)) re.2
      rw [hh]
      exact hr.2.trans_le rg.2.2
  rw [segmentDensity,if_pos rr]
  have ag := geom.2.2.2.2 i hi
  cases hs : d.aIndex i with
  | none => rfl
  | some j =>
    simp only [hs, Option.elim_some] at ag ⊢
    have ae := rankSegmentFrameCheck_endpoints hA ag.1
    have ar : r∈Ioo ((rankFrameSegment segments j).left.a:ℝ)
        (rankFrameSegment segments j).right.a := by
      constructor
      · have hh : ((rankFrameSegment segments j).left.a:ℝ)=d.aNode j := by simpa only [aNode] using congrArg (fun q : ℚ => (q : ℝ)) ae.1
        rw [hh]
        exact ag.2.1.trans_lt hr.1
      · have hh : ((rankFrameSegment segments j).right.a:ℝ)=d.aNode (j+1) := by simpa only [aNode] using congrArg (fun q : ℚ => (q : ℝ)) ae.2
        rw [hh]
        exact hr.2.trans_le ag.2.2
    rw [segmentDensity,if_pos ar]

end RankOverlayArrays
namespace ReferenceOverlayCell

def selectedCheck (c : ReferenceOverlayCell) (segments : List ReferenceSegment)
    (d : RankOverlayArrays) (i : ℕ) : Bool :=
  decide (c.lo=d.fine[i]?.getD 0 ∧ c.hi=d.fine[i+1]?.getD 0 ∧
    c.components.map (fun x=>(x.segment,x.useR))=
      [(rankFrameSegment segments (d.rIndex i),true)]++
        (d.aIndex i).toList.map (fun j=>(rankFrameSegment segments j,false)))

noncomputable def densitySum (c : ReferenceOverlayCell) (weightR weightA : ℝ→ℝ) (r : ℝ) : ℝ :=
  (c.components.map (fun x=>segmentDensity x.segment x.rank
    (if x.useR then weightR else weightA) r)).sum

theorem selectedCheck_endpoints {c : ReferenceOverlayCell} {segments : List ReferenceSegment}
    {d : RankOverlayArrays} {i : ℕ} (hc : c.selectedCheck segments d i=true) :
    (c.lo:ℝ)=d.fineNode i ∧ (c.hi:ℝ)=d.fineNode (i+1) := by
  have hh := of_decide_eq_true hc
  exact ⟨by simpa only [RankOverlayArrays.fineNode] using congrArg (fun q : ℚ => (q : ℝ)) hh.1,
    by simpa only [RankOverlayArrays.fineNode] using congrArg (fun q : ℚ => (q : ℝ)) hh.2.1⟩

theorem selectedCheck_density {c : ReferenceOverlayCell} {segments : List ReferenceSegment}
    {d : RankOverlayArrays} {i : ℕ} (hc : c.selectedCheck segments d i=true)
    (hg : d.geometryCheck=true)
    (hR : rankSegmentFrameCheck segments d.nodeR ReferenceNode.r=true)
    (hA : rankSegmentFrameCheck segments d.nodeA ReferenceNode.a=true)
    (hi : i<d.cellCount) {r : ℝ} (hr : r∈Ioo (c.lo:ℝ) c.hi)
    (weightR weightA : ℝ→ℝ) :
    pushforwardDensity segments ReferenceNode.r (fun _=>weightR) r+
      pushforwardDensity segments ReferenceNode.a (fun _=>weightA) r=
      c.densitySum weightR weightA r := by
  have hh := of_decide_eq_true hc
  have he := selectedCheck_endpoints hc
  have hr' : r∈Ioo (d.fineNode i) (d.fineNode (i+1)) := by rwa [he.1,he.2] at hr
  rw [RankOverlayArrays.pushforward_selected hg hR hA hi hr']
  let eval : ReferenceSegment×Bool→ℝ := fun x=>segmentDensity x.1
    (if x.2 then ReferenceNode.r else ReferenceNode.a) (if x.2 then weightR else weightA) r
  have hmap : c.components.map (fun x=>segmentDensity x.segment x.rank
      (if x.useR then weightR else weightA) r)=
      (c.components.map (fun x=>(x.segment,x.useR))).map eval := by
    simp only [List.map_map]
    rfl
  rw [densitySum,hmap,hh.2.2]
  cases hs : d.aIndex i <;> simp [hs,eval]

end ReferenceOverlayCell
end OptimalG.Certificates.Transport
