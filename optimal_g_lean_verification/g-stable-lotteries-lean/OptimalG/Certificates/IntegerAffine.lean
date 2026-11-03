import OptimalG.Certificates.IntegerBoxes
import OptimalG.Certificates.HighResidualTree

/-! Directed integer arithmetic accelerates the existing exact affine checks.
The final theorem implies the original rational checker; no residual statement
or downstream witness interface is changed. -/
namespace OptimalG.Certificates
namespace RatInterval

def affineMinimizer (b : RatInterval) (k : ℚ) : ℚ :=
  if k*b.lo≤k*b.hi then b.lo else b.hi

theorem affineMinimizer_mem (b : RatInterval) (k : ℚ) (hb : b.lo≤b.hi) :
    b.lo≤b.affineMinimizer k ∧ b.affineMinimizer k≤b.hi := by
  unfold affineMinimizer
  split <;> exact ⟨by first | exact le_rfl | exact hb,by first | exact le_rfl | exact hb⟩

theorem point_mul_lower (b : RatInterval) (k : ℚ) :
    ((point k).mul b).lo=k*b.affineMinimizer k := by
  simp only [mul,point,min_self]
  unfold affineMinimizer
  split_ifs with hk
  · exact min_eq_left hk
  · exact min_eq_right (le_of_not_ge hk)

end RatInterval
namespace RatBox4

def ordered (b : RatBox4) : Prop :=
  b.b0.lo≤b.b0.hi ∧ b.b1.lo≤b.b1.hi ∧ b.b2.lo≤b.b2.hi ∧ b.b3.lo≤b.b3.hi
instance (b : RatBox4) : Decidable b.ordered := inferInstanceAs (Decidable (_ ∧ _))

end RatBox4
namespace Affine4
open IntegerInterval

def minimizingCorner (f : Affine4) (b : RatBox4) : RatVector4 :=
  ⟨b.b0.affineMinimizer f.k0,b.b1.affineMinimizer f.k1,
    b.b2.affineMinimizer f.k2,b.b3.affineMinimizer f.k3⟩

theorem minimizingCorner_mem (f : Affine4) (b : RatBox4) (hb : b.ordered) :
    b.Contains (f.minimizingCorner b) := by
  have h0 := b.b0.affineMinimizer_mem f.k0 hb.1
  have h1 := b.b1.affineMinimizer_mem f.k1 hb.2.1
  have h2 := b.b2.affineMinimizer_mem f.k2 hb.2.2.1
  have h3 := b.b3.affineMinimizer_mem f.k3 hb.2.2.2
  exact ⟨h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2⟩

theorem interval_lower_eq (f : Affine4) (b : RatBox4) :
    (f.interval b).lo=f.eval (f.minimizingCorner b) := by
  simp only [interval,RatInterval.add,RatInterval.point_mul_lower,
    eval,minimizingCorner]
  rfl

def integerInterval (s : ℕ) (f : Affine4) (b : RatBox4) : IntegerInterval :=
  ((((pointRounded s f.offset).addRounded
    (mulRounded s (pointRounded s f.k0) (fromRat s b.b0))).addRounded
    (mulRounded s (pointRounded s f.k1) (fromRat s b.b1))).addRounded
    (mulRounded s (pointRounded s f.k2) (fromRat s b.b2))).addRounded
    (mulRounded s (pointRounded s f.k3) (fromRat s b.b3))

theorem integerInterval_contains {s : ℕ} (hs : 0<s) {f : Affine4}
    {b : RatBox4} {v : RatVector4} (hb : b.Contains v) :
    (f.integerInterval s b).Contains s (f.eval v:ℝ) := by
  rcases hb with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  have hc0 : b.b0.Contains (v.x0:ℝ) := ⟨by exact_mod_cast h0,by exact_mod_cast h1⟩
  have hc1 : b.b1.Contains (v.x1:ℝ) := ⟨by exact_mod_cast h2,by exact_mod_cast h3⟩
  have hc2 : b.b2.Contains (v.x2:ℝ) := ⟨by exact_mod_cast h4,by exact_mod_cast h5⟩
  have hc3 : b.b3.Contains (v.x3:ℝ) := ⟨by exact_mod_cast h6,by exact_mod_cast h7⟩
  have h := addRounded_contains (addRounded_contains (addRounded_contains
    (addRounded_contains (pointRounded_contains s f.offset)
      (mulRounded_contains hs (pointRounded_contains s f.k0) (fromRat_contains hs hc0)))
      (mulRounded_contains hs (pointRounded_contains s f.k1) (fromRat_contains hs hc1)))
      (mulRounded_contains hs (pointRounded_contains s f.k2) (fromRat_contains hs hc2)))
      (mulRounded_contains hs (pointRounded_contains s f.k3) (fromRat_contains hs hc3))
  simpa only [integerInterval,eval,Rat.cast_add,Rat.cast_mul] using h

theorem integerInterval_contains_lower {s : ℕ} (hs : 0<s) (f : Affine4)
    (b : RatBox4) (hb : b.ordered) :
    (f.integerInterval s b).Contains s ((f.interval b).lo:ℝ) := by
  rw [interval_lower_eq]
  exact integerInterval_contains hs (f.minimizingCorner_mem b hb)

def slopeDot (f : Affine4) (v : RatVector4) : ℚ :=
  f.k0*v.x0+f.k1*v.x1+f.k2*v.x2+f.k3*v.x3

def integerSlopeDot (s : ℕ) (f : Affine4) (v : RatVector4) : IntegerInterval :=
  (((mulRounded s (pointRounded s f.k0) (pointRounded s v.x0)).addRounded
    (mulRounded s (pointRounded s f.k1) (pointRounded s v.x1))).addRounded
    (mulRounded s (pointRounded s f.k2) (pointRounded s v.x2))).addRounded
    (mulRounded s (pointRounded s f.k3) (pointRounded s v.x3))

theorem integerSlopeDot_contains {s : ℕ} (hs : 0<s) (f : Affine4) (v : RatVector4) :
    (f.integerSlopeDot s v).Contains s (f.slopeDot v:ℝ) := by
  have h := addRounded_contains (addRounded_contains (addRounded_contains
    (mulRounded_contains hs (pointRounded_contains s f.k0) (pointRounded_contains s v.x0))
    (mulRounded_contains hs (pointRounded_contains s f.k1) (pointRounded_contains s v.x1)))
    (mulRounded_contains hs (pointRounded_contains s f.k2) (pointRounded_contains s v.x2)))
    (mulRounded_contains hs (pointRounded_contains s f.k3) (pointRounded_contains s v.x3))
  simpa only [integerSlopeDot,slopeDot,Rat.cast_add,Rat.cast_mul] using h

end Affine4
namespace SegmentBox4
open IntegerInterval

def integerInterval (s : ℕ) (b : SegmentBox4) (f : Affine4) : IntegerInterval :=
  (f.integerInterval s b.residuals).addRounded
    (mulRounded s (f.integerSlopeDot s b.slopes) (fromRat s b.parameter))

def integerLowerCheck (s : ℕ) (b : SegmentBox4) (f : Affine4) : Bool :=
  decide (b.residuals.ordered ∧ b.parameter.lo≤b.parameter.hi) &&
    decide (0≤(b.integerInterval s f).lo)

theorem integerInterval_contains_lower {s : ℕ} (hs : 0<s) (b : SegmentBox4)
    (f : Affine4) (hb : b.residuals.ordered) (hp : b.parameter.lo≤b.parameter.hi) :
    (b.integerInterval s f).Contains s ((b.interval f).lo:ℝ) := by
  have hm := b.parameter.affineMinimizer_mem (f.slopeDot b.slopes) hp
  have hr : b.parameter.Contains (b.parameter.affineMinimizer (f.slopeDot b.slopes):ℝ) :=
    ⟨by exact_mod_cast hm.1,by exact_mod_cast hm.2⟩
  have h := addRounded_contains (f.integerInterval_contains_lower hs b.residuals hb)
    (mulRounded_contains hs (f.integerSlopeDot_contains hs b.slopes) (fromRat_contains hs hr))
  have he : (b.interval f).lo=(f.interval b.residuals).lo+
      f.slopeDot b.slopes*b.parameter.affineMinimizer (f.slopeDot b.slopes) := by
    simp only [interval,RatInterval.add,RatInterval.point_mul_lower,Affine4.slopeDot]
  rw [he]
  simpa only [integerInterval,Rat.cast_add,Rat.cast_mul] using h

/-- The rounded lower bound is conservative relative to the original exact
rational minimum, not merely relative to a sampled point. -/
theorem integerLowerCheck_implies {s : ℕ} (hs : 0<s) {b : SegmentBox4} {f : Affine4}
    (hc : b.integerLowerCheck s f=true) : b.lowerCheck f=true := by
  have hh : (b.residuals.ordered ∧ b.parameter.lo≤b.parameter.hi) ∧
      0≤(b.integerInterval s f).lo := by
    simpa only [integerLowerCheck,Bool.and_eq_true,decide_eq_true_eq] using hc
  have h := (b.integerInterval_contains_lower hs f hh.1.1 hh.1.2).1
  have hlo : (0:ℝ)≤(b.integerInterval s f).lo := by exact_mod_cast hh.2
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  have hl : (0:ℝ)≤((b.interval f).lo:ℝ) := by nlinarith
  apply decide_eq_true_eq.mpr
  exact_mod_cast hl

end SegmentBox4
namespace SegmentTree

def integerFormsCheck (s : ℕ) (forms : List Affine4) : SegmentTree→Bool
  | .leaf b ns => if forms.all (fun f => b.integerLowerCheck s f) then true
      else ns.all (fun n => forms.all (fun f => decide (0≤f.eval (layerFeatures n))))
  | .branch b l r => if forms.all (fun f => b.integerLowerCheck s f) then true
      else integerFormsCheck s forms l && integerFormsCheck s forms r

theorem integerFormsCheck_implies {s : ℕ} (hs : 0<s) {forms : List Affine4}
    {tree : SegmentTree} (hc : tree.integerFormsCheck s forms=true) :
    tree.formsCheck forms=true := by
  have hbox : ∀ b : SegmentBox4,
      forms.all (fun f => b.integerLowerCheck s f)=true→
        forms.all (fun f => b.lowerCheck f)=true := by
    intro b hb
    apply List.all_eq_true.mpr
    intro f hf
    exact SegmentBox4.integerLowerCheck_implies hs (List.all_eq_true.mp hb f hf)
  induction tree with
  | leaf b ns =>
    unfold integerFormsCheck at hc
    split at hc
    next hb => simp only [formsCheck,hbox b hb,if_true]
    next hb =>
      unfold formsCheck
      split
      · rfl
      · exact hc
  | branch b l r ihl ihr =>
    unfold integerFormsCheck at hc
    split at hc
    next hb => simp only [formsCheck,hbox b hb,if_true]
    next hb =>
      unfold formsCheck
      split
      · rfl
      · exact Bool.and_eq_true_iff.mpr ⟨ihl (Bool.and_eq_true_iff.mp hc).1,
          ihr (Bool.and_eq_true_iff.mp hc).2⟩

def integerResidualCheck (s : ℕ) (tree : SegmentTree) (q : CubicPiece)
    (L S penalty : ℚ) : Bool := tree.integerFormsCheck s (q.residualForms L S penalty)

theorem integerResidualCheck_implies {s : ℕ} (hs : 0<s) {tree : SegmentTree}
    {q : CubicPiece} {L S penalty : ℚ}
    (hc : tree.integerResidualCheck s q L S penalty=true) :
    tree.residualCheck q L S penalty=true := integerFormsCheck_implies hs hc

end SegmentTree
end OptimalG.Certificates
