import OptimalG.Certificates.LayerNode
import OptimalG.Certificates.SegmentBox
import OptimalG.Certificates.FeatureTree

/-! A checked feature tree compresses simultaneous inequalities over all layer nodes. -/
namespace OptimalG.Certificates

inductive SegmentTree where
  | leaf (box : SegmentBox4) (entries : List LayerNode)
  | branch (box : SegmentBox4) (left right : SegmentTree)
  deriving Repr

namespace SegmentTree

def box : SegmentTree → SegmentBox4
  | .leaf b _ => b
  | .branch b _ _ => b

def entries : SegmentTree → List LayerNode
  | .leaf _ ns => ns
  | .branch _ l r => l.entries++r.entries

def check : SegmentTree → Bool
  | .leaf b ns => ns.all (fun n => b.containsCheck (layerFeatures n) n.p)
  | .branch b l r => l.box.subsetCheck b && (r.box.subsetCheck b && (l.check && r.check))

theorem check_contains {tree : SegmentTree} (hc : tree.check=true) {n : LayerNode}
    (hn : n∈tree.entries) : tree.box.Contains (layerFeatures n) n.p := by
  induction tree with
  | leaf b ns => exact of_decide_eq_true (List.all_eq_true.mp hc n hn)
  | branch b l r ihl ihr =>
    have hh : l.box.subsetCheck b=true ∧ r.box.subsetCheck b=true ∧ l.check=true ∧ r.check=true := by
      simpa only [check,Bool.and_eq_true] using hc
    rcases List.mem_append.mp hn with hl | hr
    · exact SegmentBox4.subsetCheck_contains (ihl hh.2.2.1 hl) hh.1
    · exact SegmentBox4.subsetCheck_contains (ihr hh.2.2.2 hr) hh.2.1

def formsCheck (forms : List Affine4) : SegmentTree → Bool
  | .leaf b ns => if forms.all (fun f => b.lowerCheck f) then true
      else ns.all (fun n => forms.all (fun f => decide (0≤f.eval (layerFeatures n))))
  | .branch b l r => if forms.all (fun f => b.lowerCheck f) then true
      else formsCheck forms l && formsCheck forms r

/-- Each accepted affine form is nonnegative at every layer node in the tree.
All pruning uses checked rational boxes, and leaf fallbacks check exact values. -/
theorem formsCheck_sound {forms : List Affine4} {tree : SegmentTree}
    (ht : tree.check=true) (hc : tree.formsCheck forms=true)
    {n : LayerNode} (hn : n∈tree.entries) {f : Affine4} (hf : f∈forms) :
    0≤f.eval (layerFeatures n) := by
  induction tree with
  | leaf b ns =>
    unfold formsCheck at hc
    split at hc
    next hb =>
      have h := List.all_eq_true.mp hb f hf
      exact SegmentBox4.lowerCheck_sound h (check_contains ht hn)
    next hb =>
      have h := List.all_eq_true.mp (List.all_eq_true.mp hc n hn) f hf
      exact of_decide_eq_true h
  | branch b l r ihl ihr =>
    unfold formsCheck at hc
    split at hc
    next hb =>
      have h := List.all_eq_true.mp hb f hf
      exact SegmentBox4.lowerCheck_sound h (check_contains ht hn)
    next hb =>
      have ht' : l.box.subsetCheck b=true ∧ r.box.subsetCheck b=true ∧ l.check=true ∧ r.check=true := by
        simpa only [check,Bool.and_eq_true] using ht
      have hc' : l.formsCheck forms=true ∧ r.formsCheck forms=true := by
        simpa only [Bool.and_eq_true] using hc
      rcases List.mem_append.mp hn with hl | hr
      · exact ihl ht'.2.2.1 hc'.1 hl
      · exact ihr ht'.2.2.2 hc'.2 hr

end SegmentTree
end OptimalG.Certificates
