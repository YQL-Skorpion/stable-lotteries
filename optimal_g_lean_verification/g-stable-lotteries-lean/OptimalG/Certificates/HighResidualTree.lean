import OptimalG.Certificates.SegmentTree
import OptimalG.Certificates.HighPiece

/-! Simultaneous exact polynomial residual bounds against every layer node. -/
namespace OptimalG.Certificates

namespace CubicPiece

def residualForm0 (q : CubicPiece) (L S penalty : ℚ) : Affine4 :=
  ⟨-penalty-q.a0,L-q.lo,q.f0-L*q.lo+q.lo^2/2+S,L-q.lo,1/2⟩
def residualForm1 (q : CubicPiece) (L : ℚ) : Affine4 :=
  ⟨-q.a1*q.length,-q.length,(q.a0-L+q.lo)*q.length,-q.length,0⟩
def residualForm2 (q : CubicPiece) : Affine4 :=
  ⟨-q.a2*q.length^2,0,(q.a1+1)/2*q.length^2,0,0⟩
def residualForm3 (q : CubicPiece) : Affine4 :=
  ⟨-q.a3*q.length^3,0,q.a2/3*q.length^3,0,0⟩
def residualForm4 (q : CubicPiece) : Affine4 :=
  ⟨0,0,q.a3/4*q.length^4,0,0⟩

def residualForms (q : CubicPiece) (L S penalty : ℚ) : List Affine4 :=
  let a:=q.residualForm0 L S penalty
  let b:=q.residualForm1 L
  let c:=q.residualForm2
  let d:=q.residualForm3
  let e:=q.residualForm4
  [a,a.add (b.scale (1/5)),(a.add (b.scale (2/5))).add (c.scale (1/10)),
   ((a.add (b.scale (3/5))).add (c.scale (3/10))).add (d.scale (1/10)),
   (((a.add (b.scale (4/5))).add (c.scale (3/5))).add (d.scale (2/5))).add (e.scale (1/5)),
   (((a.add b).add c).add d).add e]

theorem residualForms_eval (q : CubicPiece) (L S penalty : ℚ) (n : LayerNode) :
    (q.residualForms L S penalty).map (fun f => f.eval (layerFeatures n))=
      let p:=q.highResidual L S penalty n.p n.Cu n.alphau
      [p.b0,p.b1,p.b2,p.b3,p.b4,p.b5] := by
  apply List.ext_getElem (by simp [residualForms])
  intro i hleft hright
  have hi : i<6 := by simpa using hright
  interval_cases i <;>
    norm_num [residualForms,residualForm0,residualForm1,residualForm2,residualForm3,residualForm4,
      Affine4.eval,Affine4.add,Affine4.scale,layerFeatures,highResidual,
      PowerPolynomial5.b0,PowerPolynomial5.b1,PowerPolynomial5.b2,PowerPolynomial5.b3,
      PowerPolynomial5.b4,PowerPolynomial5.b5] <;> ring

theorem residualForms_nonnegative {q : CubicPiece} {L S penalty : ℚ} {n : LayerNode}
    (hc : ∀ f∈q.residualForms L S penalty, 0≤f.eval (layerFeatures n)) :
    (q.highResidual L S penalty n.p n.Cu n.alphau).nonnegativeCheck=true := by
  let p:=q.highResidual L S penalty n.p n.Cu n.alphau
  have hb : ∀ v∈[p.b0,p.b1,p.b2,p.b3,p.b4,p.b5], (0:ℚ)≤v := by
    rw [← residualForms_eval q L S penalty n]
    intro v hv
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hv
    exact hc f hf
  apply decide_eq_true_eq.mpr
  exact ⟨hb _ (by simp [p]),hb _ (by simp [p]),hb _ (by simp [p]),hb _ (by simp [p]),hb _ (by simp [p]),hb _ (by simp [p])⟩

end CubicPiece

namespace SegmentTree

def residualCheck (tree : SegmentTree) (q : CubicPiece) (L S penalty : ℚ) : Bool :=
  tree.formsCheck (q.residualForms L S penalty)

theorem residualCheck_sound {tree : SegmentTree} (ht : tree.check=true)
    {q : CubicPiece} {L S penalty : ℚ} (hc : tree.residualCheck q L S penalty=true)
    {n : LayerNode} (hn : n∈tree.entries) :
    (q.highResidual L S penalty n.p n.Cu n.alphau).nonnegativeCheck=true := by
  apply CubicPiece.residualForms_nonnegative
  intro f hf
  exact formsCheck_sound ht hc hn hf

end SegmentTree
end OptimalG.Certificates
