import OptimalG.Certificates.LayerNode
import OptimalG.Certificates.AffineBox

/-! A checked feature tree compresses simultaneous inequalities over all layer nodes. -/
namespace OptimalG.Certificates

def layerFeatures (n : LayerNode) : RatVector4 :=
  ⟨n.Cu,n.alphau,n.alphau*n.p,n.alphau*n.p^2⟩

inductive FeatureTree where
  | leaf (box : RatBox4) (entries : List LayerNode)
  | branch (box : RatBox4) (left right : FeatureTree)
  deriving Repr

namespace FeatureTree

def box : FeatureTree → RatBox4
  | .leaf b _ => b
  | .branch b _ _ => b

def entries : FeatureTree → List LayerNode
  | .leaf _ ns => ns
  | .branch _ l r => l.entries++r.entries

def check : FeatureTree → Bool
  | .leaf b ns => ns.all (fun n => b.containsCheck (layerFeatures n))
  | .branch b l r => l.box.subsetCheck b && (r.box.subsetCheck b && (l.check && r.check))

theorem check_contains {tree : FeatureTree} (hc : tree.check=true) {n : LayerNode}
    (hn : n∈tree.entries) : tree.box.Contains (layerFeatures n) := by
  induction tree with
  | leaf b ns => exact of_decide_eq_true (List.all_eq_true.mp hc n hn)
  | branch b l r ihl ihr =>
    have hh : l.box.subsetCheck b=true ∧ r.box.subsetCheck b=true ∧ l.check=true ∧ r.check=true := by
      simpa only [check,Bool.and_eq_true] using hc
    rcases List.mem_append.mp hn with hl | hr
    · exact RatBox4.subsetCheck_contains (ihl hh.2.2.1 hl) hh.1
    · exact RatBox4.subsetCheck_contains (ihr hh.2.2.2 hr) hh.2.1

def formsCheck (forms : List Affine4) : FeatureTree → Bool
  | .leaf b ns => if forms.all (fun f => f.lowerCheck b) then true
      else ns.all (fun n => forms.all (fun f => decide (0≤f.eval (layerFeatures n))))
  | .branch b l r => if forms.all (fun f => f.lowerCheck b) then true
      else formsCheck forms l && formsCheck forms r

/-- Each accepted affine form is nonnegative at every layer node in the tree.
All pruning uses checked rational boxes, and leaf fallbacks check exact values. -/
theorem formsCheck_sound {forms : List Affine4} {tree : FeatureTree}
    (ht : tree.check=true) (hc : tree.formsCheck forms=true)
    {n : LayerNode} (hn : n∈tree.entries) {f : Affine4} (hf : f∈forms) :
    0≤f.eval (layerFeatures n) := by
  induction tree with
  | leaf b ns =>
    unfold formsCheck at hc
    split at hc
    next hb =>
      have h := List.all_eq_true.mp hb f hf
      exact Affine4.lowerCheck_sound h (check_contains ht hn)
    next hb =>
      have h := List.all_eq_true.mp (List.all_eq_true.mp hc n hn) f hf
      exact of_decide_eq_true h
  | branch b l r ihl ihr =>
    unfold formsCheck at hc
    split at hc
    next hb =>
      have h := List.all_eq_true.mp hb f hf
      exact Affine4.lowerCheck_sound h (check_contains ht hn)
    next hb =>
      have ht' : l.box.subsetCheck b=true ∧ r.box.subsetCheck b=true ∧ l.check=true ∧ r.check=true := by
        simpa only [check,Bool.and_eq_true] using ht
      have hc' : l.formsCheck forms=true ∧ r.formsCheck forms=true := by
        simpa only [Bool.and_eq_true] using hc
      rcases List.mem_append.mp hn with hl | hr
      · exact ihl ht'.2.2.1 hc'.1 hl
      · exact ihr ht'.2.2.2 hc'.2 hr

end FeatureTree
end OptimalG.Certificates
