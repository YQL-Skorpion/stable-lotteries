import OptimalG.Certificates.IntegerAffine

/-! Literal integer caches move rational-to-integer conversion outside the
recursive affine checks. Cache validation is exact, and accepted fast checks
imply the existing integer checker without changing its leaf fallback. -/
namespace OptimalG.Certificates
open IntegerInterval

structure IntegerBox4 where
  b0 : IntegerInterval
  b1 : IntegerInterval
  b2 : IntegerInterval
  b3 : IntegerInterval
  deriving DecidableEq, Repr

namespace IntegerBox4

def ofRational (s : ℕ) (b : RatBox4) : IntegerBox4 :=
  ⟨fromRat s b.b0,fromRat s b.b1,fromRat s b.b2,fromRat s b.b3⟩

def ofVector (s : ℕ) (v : RatVector4) : IntegerBox4 :=
  ⟨pointRounded s v.x0,pointRounded s v.x1,pointRounded s v.x2,pointRounded s v.x3⟩

end IntegerBox4

structure IntegerAffine4 where
  offset : IntegerInterval
  k0 : IntegerInterval
  k1 : IntegerInterval
  k2 : IntegerInterval
  k3 : IntegerInterval
  deriving DecidableEq, Repr

namespace IntegerAffine4

def ofRational (s : ℕ) (f : Affine4) : IntegerAffine4 :=
  ⟨pointRounded s f.offset,pointRounded s f.k0,pointRounded s f.k1,
    pointRounded s f.k2,pointRounded s f.k3⟩

def interval (s : ℕ) (f : IntegerAffine4) (b : IntegerBox4) : IntegerInterval :=
  (((f.offset.addRounded (mulRounded s f.k0 b.b0)).addRounded
    (mulRounded s f.k1 b.b1)).addRounded (mulRounded s f.k2 b.b2)).addRounded
    (mulRounded s f.k3 b.b3)

def slopeDot (s : ℕ) (f : IntegerAffine4) (v : IntegerBox4) : IntegerInterval :=
  (((mulRounded s f.k0 v.b0).addRounded (mulRounded s f.k1 v.b1)).addRounded
    (mulRounded s f.k2 v.b2)).addRounded (mulRounded s f.k3 v.b3)

theorem interval_ofRational (s : ℕ) (f : Affine4) (b : RatBox4) :
    (ofRational s f).interval s (IntegerBox4.ofRational s b)=f.integerInterval s b := rfl

theorem slopeDot_ofRational (s : ℕ) (f : Affine4) (v : RatVector4) :
    (ofRational s f).slopeDot s (IntegerBox4.ofVector s v)=f.integerSlopeDot s v := rfl

end IntegerAffine4

structure IntegerSegmentBox4 where
  parameter : IntegerInterval
  slopes : IntegerBox4
  residuals : IntegerBox4
  deriving DecidableEq, Repr

namespace IntegerSegmentBox4

def ofRational (s : ℕ) (b : SegmentBox4) : IntegerSegmentBox4 :=
  ⟨fromRat s b.parameter,IntegerBox4.ofVector s b.slopes,IntegerBox4.ofRational s b.residuals⟩

def cacheCheck (s : ℕ) (b : SegmentBox4) (cached : IntegerSegmentBox4) : Bool :=
  decide (cached=ofRational s b ∧ b.residuals.ordered ∧ b.parameter.lo≤b.parameter.hi)

def interval (s : ℕ) (b : IntegerSegmentBox4) (f : IntegerAffine4) : IntegerInterval :=
  (f.interval s b.residuals).addRounded (mulRounded s (f.slopeDot s b.slopes) b.parameter)

def lowerCheck (s : ℕ) (b : IntegerSegmentBox4) (f : IntegerAffine4) : Bool :=
  decide (0≤(b.interval s f).lo)

theorem interval_ofRational (s : ℕ) (b : SegmentBox4) (f : Affine4) :
    (ofRational s b).interval s (IntegerAffine4.ofRational s f)=b.integerInterval s f := rfl

theorem lowerCheck_eq {s : ℕ} {b : SegmentBox4} {cached : IntegerSegmentBox4}
    (hc : cacheCheck s b cached=true) (f : Affine4) :
    cached.lowerCheck s (IntegerAffine4.ofRational s f)=b.integerLowerCheck s f := by
  have hh := of_decide_eq_true hc
  rcases hh with ⟨rfl,hb,hp⟩
  simp [lowerCheck,interval_ofRational,SegmentBox4.integerLowerCheck,hb,hp]

end IntegerSegmentBox4

inductive IntegerSegmentTree where
  | leaf (box : IntegerSegmentBox4)
  | branch (box : IntegerSegmentBox4) (left right : IntegerSegmentTree)
  deriving Repr

namespace IntegerSegmentTree

def ofRational (s : ℕ) : SegmentTree→IntegerSegmentTree
  | .leaf b _ => .leaf (IntegerSegmentBox4.ofRational s b)
  | .branch b l r => .branch (IntegerSegmentBox4.ofRational s b) (ofRational s l) (ofRational s r)

def cacheCheck (s : ℕ) : SegmentTree→IntegerSegmentTree→Bool
  | .leaf b _, .leaf c => IntegerSegmentBox4.cacheCheck s b c
  | .branch b l r, .branch c cl cr =>
      IntegerSegmentBox4.cacheCheck s b c && (cacheCheck s l cl && cacheCheck s r cr)
  | _,_ => false

def formsCacheCheck (s : ℕ) (forms : List Affine4) (cached : List IntegerAffine4) : Bool :=
  decide (cached=forms.map (IntegerAffine4.ofRational s))

/-- The original rational forms occur only in the unchanged exact fallback.
All internal-node arithmetic uses literal integer fields. -/
def fastFormsCheck (s : ℕ) (forms : List Affine4) (cachedForms : List IntegerAffine4) :
    SegmentTree→IntegerSegmentTree→Bool
  | .leaf _ ns, .leaf c =>
      if cachedForms.all (fun f => c.lowerCheck s f) then true
      else ns.all (fun n => forms.all (fun f => decide (0≤f.eval (layerFeatures n))))
  | .branch _ l r, .branch c cl cr =>
      if cachedForms.all (fun f => c.lowerCheck s f) then true
      else fastFormsCheck s forms cachedForms l cl && fastFormsCheck s forms cachedForms r cr
  | _,_ => false

private theorem box_all_eq {s : ℕ} {b : SegmentBox4} {c : IntegerSegmentBox4}
    (hc : IntegerSegmentBox4.cacheCheck s b c=true) (forms : List Affine4) :
    (forms.map (IntegerAffine4.ofRational s)).all (fun f => c.lowerCheck s f)=
      forms.all (fun f => b.integerLowerCheck s f) := by
  simp only [List.all_map,Function.comp_def]
  congr 1
  funext f
  exact IntegerSegmentBox4.lowerCheck_eq hc f

/-- Exact Boolean equality makes this accelerator interchangeable with the
previous integer checker, including its successful fallback leaves. -/
theorem fastFormsCheck_eq {s : ℕ} {forms : List Affine4} {cachedForms : List IntegerAffine4}
    (hf : formsCacheCheck s forms cachedForms=true) (tree : SegmentTree) :
    ∀ cached,cacheCheck s tree cached=true →
      fastFormsCheck s forms cachedForms tree cached=tree.integerFormsCheck s forms := by
  have he : cachedForms=forms.map (IntegerAffine4.ofRational s) := of_decide_eq_true hf
  subst cachedForms
  induction tree with
  | leaf b ns =>
    intro cached hc
    cases cached with
    | leaf c =>
      simp only [cacheCheck] at hc
      simp only [fastFormsCheck,SegmentTree.integerFormsCheck,box_all_eq hc forms]
    | branch c cl cr => simp only [cacheCheck,Bool.false_eq_true] at hc
  | branch b l r ihl ihr =>
    intro cached hc
    cases cached with
    | leaf c => simp only [cacheCheck,Bool.false_eq_true] at hc
    | branch c cl cr =>
      have hh := Bool.and_eq_true_iff.mp hc
      have hchildren := Bool.and_eq_true_iff.mp hh.2
      simp only [fastFormsCheck,SegmentTree.integerFormsCheck,box_all_eq hh.1 forms,
        ihl cl hchildren.1,ihr cr hchildren.2]

theorem fastFormsCheck_implies {s : ℕ} {forms : List Affine4}
    {cachedForms : List IntegerAffine4} {tree : SegmentTree} {cached : IntegerSegmentTree}
    (hf : formsCacheCheck s forms cachedForms=true) (ht : cacheCheck s tree cached=true)
    (hc : fastFormsCheck s forms cachedForms tree cached=true) :
    tree.integerFormsCheck s forms=true := by
  rwa [fastFormsCheck_eq hf tree cached ht] at hc

def fastResidualCheck (s : ℕ) (tree : SegmentTree) (cached : IntegerSegmentTree)
    (q : CubicPiece) (L S penalty : ℚ) (forms : List IntegerAffine4) : Bool :=
  fastFormsCheck s (q.residualForms L S penalty) forms tree cached

theorem fastResidualCheck_implies {s : ℕ} {tree : SegmentTree} {cached : IntegerSegmentTree}
    {q : CubicPiece} {L S penalty : ℚ} {forms : List IntegerAffine4}
    (hf : formsCacheCheck s (q.residualForms L S penalty) forms=true)
    (ht : cacheCheck s tree cached=true)
    (hc : fastResidualCheck s tree cached q L S penalty forms=true) :
    tree.integerResidualCheck s q L S penalty=true := fastFormsCheck_implies hf ht hc

end IntegerSegmentTree
end OptimalG.Certificates
