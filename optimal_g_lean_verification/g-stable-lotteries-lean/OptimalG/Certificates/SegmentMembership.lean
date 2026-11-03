import OptimalG.Certificates.SegmentTree
import OptimalG.Certificates.ContinuousLayerPolynomials

/-! Logarithmic-depth membership proposals for the layer segment tree. The
search chooses one subtree by the node parameter; soundness requires no global
ordering premise because the selected leaf still checks the complete node. -/
namespace OptimalG.Certificates
namespace SegmentTree

/-- Follow one parameter-directed branch and check full equality in its leaf.
A misplaced node can cause rejection, but can never cause a false acceptance. -/
def nodeCheck : SegmentTree → LayerNode → Bool
  | .leaf _ ns, n => decide (n ∈ ns)
  | .branch _ left right, n =>
      if n.p ≤ left.box.parameter.hi then left.nodeCheck n else right.nodeCheck n

theorem nodeCheck_sound {tree : SegmentTree} {n : LayerNode}
    (hc : tree.nodeCheck n = true) : n ∈ tree.entries := by
  induction tree with
  | leaf b ns => exact of_decide_eq_true hc
  | branch b left right ihl ihr =>
      unfold nodeCheck at hc
      change n ∈ left.entries ++ right.entries
      split at hc
      · exact List.mem_append.mpr (Or.inl (ihl hc))
      · exact List.mem_append.mpr (Or.inr (ihr hc))

end SegmentTree

/-- Each continuous layer cell uses two endpoint nodes contained in the checked
segment tree. Each node lookup visits only a single branch at every level. -/
def endpointMembershipCheck (tree : SegmentTree) (cells : List ContinuousLayerCell) : Bool :=
  cells.all fun c => tree.nodeCheck c.left && tree.nodeCheck c.right

theorem endpointMembershipCheck_sound {tree : SegmentTree} {cells : List ContinuousLayerCell}
    (hc : endpointMembershipCheck tree cells = true) {c : ContinuousLayerCell} (hmem : c ∈ cells) :
    c.left ∈ tree.entries ∧ c.right ∈ tree.entries := by
  have hh := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hc c hmem)
  exact ⟨SegmentTree.nodeCheck_sound hh.1,SegmentTree.nodeCheck_sound hh.2⟩

@[simp] theorem endpointMembershipCheck_append (tree : SegmentTree)
    (left right : List ContinuousLayerCell) :
    endpointMembershipCheck tree (left ++ right) =
      (endpointMembershipCheck tree left && endpointMembershipCheck tree right) := by
  simp [endpointMembershipCheck]

/-- Separately checked cell batches assemble without repeating any node lookup. -/
theorem endpointMembershipCheck_flatten {tree : SegmentTree}
    {batches : List (List ContinuousLayerCell)}
    (hc : ∀ cells ∈ batches, endpointMembershipCheck tree cells = true) :
    endpointMembershipCheck tree batches.flatten = true := by
  induction batches with
  | nil => simp [endpointMembershipCheck]
  | cons cells batches ih =>
      rw [List.flatten_cons,endpointMembershipCheck_append]
      exact Bool.and_eq_true_iff.mpr ⟨hc cells List.mem_cons_self,
        ih (fun cs hcs => hc cs (List.mem_cons_of_mem cells hcs))⟩

end OptimalG.Certificates
