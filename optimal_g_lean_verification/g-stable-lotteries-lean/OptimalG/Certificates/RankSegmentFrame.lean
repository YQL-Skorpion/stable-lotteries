import OptimalG.VariationalReferencePartition

/-! Exact list-indexed frame checks connect a finite reference segment list
to its rank endpoint array. Out-of-range getters are harmless: every checked
cell index is strictly below the actual segment-list length. -/
namespace OptimalG.Certificates.Transport

def rankFrameSegment (segments : List ReferenceSegment) (i : ℕ) : ReferenceSegment :=
  segments[i]?.getD ⟨⟨0,0,0⟩,⟨0,0,0⟩⟩

def rankSegmentFrameCellCheck (segments : List ReferenceSegment) (nodes : List ℚ)
    (rank : ReferenceNode→ℚ) (i : ℕ) : Bool :=
  decide (rank (rankFrameSegment segments i).left=nodes[i]?.getD 0 ∧
    rank (rankFrameSegment segments i).right=nodes[i+1]?.getD 0)

def rankSegmentFrameCheck (segments : List ReferenceSegment) (nodes : List ℚ)
    (rank : ReferenceNode→ℚ) : Bool :=
  decide (nodes.length=segments.length+1) &&
    (List.range segments.length).all (rankSegmentFrameCellCheck segments nodes rank)

theorem rankSegmentFrameCheck_of_parts {segments : List ReferenceSegment} {nodes : List ℚ}
    {rank : ReferenceNode→ℚ} (hlen : nodes.length=segments.length+1)
    (hc : ∀ i<segments.length,rankSegmentFrameCellCheck segments nodes rank i=true) :
    rankSegmentFrameCheck segments nodes rank=true := by
  simp only [rankSegmentFrameCheck,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨hlen,List.all_eq_true.mpr (fun i hi=>hc i (List.mem_range.mp hi))⟩

theorem rankFrameSegment_ofFn (segments : List ReferenceSegment) :
    List.ofFn (fun i : Fin segments.length=>rankFrameSegment segments i)=segments := by
  calc
    _=List.ofFn (fun i : Fin segments.length=>segments[i.val]) := by
      congr 1
      funext i
      simp only [rankFrameSegment,List.getElem?_eq_getElem i.isLt,Option.getD_some]
    _=segments := List.ofFn_getElem

theorem rankSegmentFrameCheck_density {segments : List ReferenceSegment} {nodes : List ℚ}
    {rank : ReferenceNode→ℚ} (hc : rankSegmentFrameCheck segments nodes rank=true)
    (weight : ReferenceSegment→ℝ→ℝ) (r : ℝ) :
    pushforwardDensity segments rank weight r=
      Variational.rankPartitionDensity (nodes.length-1) (fun i=>(nodes[i]?.getD 0:ℝ))
        (fun i r=>weight (rankFrameSegment segments i)
          ((rankFrameSegment segments i).inverseRankMap rank r)/
          ((rankFrameSegment segments i).slope rank:ℝ)) r := by
  obtain ⟨hlen,hcells⟩ := Bool.and_eq_true_iff.mp hc
  have hsize : nodes.length=segments.length+1 := of_decide_eq_true hlen
  have hcell (i : ℕ) (hi : i<segments.length) :=
    of_decide_eq_true (List.all_eq_true.mp hcells i (List.mem_range.mpr hi))
  have hh := Variational.pushforwardDensity_ofFn_eq_rankPartitionDensity
    (n:=segments.length) (rankFrameSegment segments) rank (fun i=>(nodes[i]?.getD 0:ℝ)) weight
    (fun i hi=>by exact_mod_cast (hcell i hi).1)
    (fun i hi=>by exact_mod_cast (hcell i hi).2) r
  rw [rankFrameSegment_ofFn] at hh
  simpa only [hsize,Nat.add_sub_cancel] using hh

end OptimalG.Certificates.Transport
