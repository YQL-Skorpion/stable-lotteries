import OptimalG.Certificates.StaticLayerPolynomials

/-! Geometric branch conditions for a continuous supporting cell. -/
namespace OptimalG.Certificates.StaticSupport
open RationalPolynomial Set
open StaticLow (lam slack leftContact rightContact)

/-- The selected polynomial is the true trial score at every interior convex
combination of the proposed endpoints. Index 242 denotes the quadratic tail. -/
def profileRangeCheck (i : ℕ) (a b : ℚ) : Bool :=
  if i<242 then affineRangeCheck (profilePiece i).lo (profilePiece i).hi a b
  else decide (i=242) && affineRangeCheck rightContact (max a b) a b

namespace ContinuousLayerCell

def b0 (c : ContinuousLayerCell) : ℚ := if c.bIsA then c.a0 else c.lo
def b1 (c : ContinuousLayerCell) : ℚ := if c.bIsA then c.a1 else c.hi

def primitiveGeometryCheck (c : ContinuousLayerCell) : Bool :=
  match c.rBranch with
  | .cap => decide (c.hi≤leftContact)
  | .piece i => decide (i<242) && profileRangeCheck i c.lo c.hi
  | .tail => affineRangeCheck rightContact (max c.lo c.hi) c.lo c.hi

def geometryCheck (c : ContinuousLayerCell) : Bool :=
  decide (c.lo<c.hi ∧ c.left.p≤c.lo ∧ c.hi≤c.right.p ∧
    (1/4:ℚ)≤c.left.p ∧ c.right.p≤9/25 ∧ c.left.p<c.right.p ∧
    c.right.p-c.left.p≤3/10000 ∧ c.left.alphau≤3 ∧
    |(c.right.alphau-c.left.alphau)/(c.right.p-c.left.p)|≤2) &&
  ((if c.bIsA then decide (c.lo≤c.a0 ∧ c.hi≤c.a1)
    else decide (c.a0≤c.lo ∧ c.a1≤c.hi)) &&
  (c.primitiveGeometryCheck &&
  (if c.pinned then decide (c.a0=leftContact ∧ c.a1=leftContact ∧
      c.aPiece=0 ∧ c.bPiece=0 ∧ c.bIsA=true)
   else decide (c.aPiece<242) && (profileRangeCheck c.aPiece c.a0 c.a1 && profileRangeCheck c.bPiece c.b0 c.b1))))

@[simp] theorem pPoly_eval (c : ContinuousLayerCell) (t : ℝ) :
    c.pPoly.eval t=(c.lo:ℝ)+((c.hi:ℝ)-c.lo)*t := by
  simp [pPoly,RationalPolynomial.eval]
  <;> ring

@[simp] theorem aPoly_eval (c : ContinuousLayerCell) (t : ℝ) :
    c.aPoly.eval t=(c.a0:ℝ)+((c.a1:ℝ)-c.a0)*t := by
  simp [aPoly,RationalPolynomial.eval]
  <;> ring

@[simp] theorem bPoly_eval (c : ContinuousLayerCell) (t : ℝ) :
    c.bPoly.eval t=(c.b0:ℝ)+((c.b1:ℝ)-c.b0)*t := by
  unfold bPoly b0 b1
  split <;> simp [pPoly_eval,aPoly_eval]

theorem scorePoly_piece_eval {i : ℕ} (hi : i<242) (r : RationalPolynomial) (t : ℝ) :
    (scorePoly i r).eval t=(profilePiece i).score (r.eval t-(profilePiece i).lo) := by
  simp only [scorePoly,if_pos hi,eval_compose,eval_add,RationalPolynomial.eval,
    Rat.cast_neg,CubicPiece.score]
  ring

theorem slopePoly_piece_eval {i : ℕ} (hi : i<242) (r : RationalPolynomial) (t : ℝ) :
    (slopePoly i r).eval t=(profilePiece i).slope (r.eval t-(profilePiece i).lo) := by
  simp only [slopePoly,if_pos hi,eval_compose,eval_add,RationalPolynomial.eval,
    Rat.cast_neg,Rat.cast_mul,Rat.cast_ofNat,CubicPiece.slope]
  ring

theorem scorePoly_tail_eval {i : ℕ} (hi : ¬i<242) (r : RationalPolynomial) (t : ℝ) :
    (scorePoly i r).eval t=(lam:ℝ)-r.eval t := by
  simp [scorePoly,hi,eval_add,eval_scale,RationalPolynomial.eval]
  <;> ring

end ContinuousLayerCell

/-- Exact actual-score semantics of each admitted polynomial branch. -/
theorem profileRangeCheck_score {i : ℕ} {a b : ℚ} (hc : profileRangeCheck i a b=true)
    {t : ℝ} (ht : t∈Ioo 0 1) :
    (ContinuousLayerCell.scorePoly i [a,b-a]).eval t=
      StaticLow.score ((a:ℝ)+((b:ℝ)-a)*t) := by
  have he : RationalPolynomial.eval [a,b-a] t=(a:ℝ)+((b:ℝ)-a)*t := by
    simp [RationalPolynomial.eval]
    <;> ring
  by_cases hi : i<242
  · have hr := affineRangeCheck_sound (show affineRangeCheck (profilePiece i).lo (profilePiece i).hi a b=true by
      simpa only [profileRangeCheck,if_pos hi] using hc) ht
    rw [ContinuousLayerCell.scorePoly_piece_eval hi,he]
    exact (StaticLow.piece_values hi hr).1.symm
  · have hh : i=242 ∧ affineRangeCheck rightContact (max a b) a b=true := by
      simpa only [profileRangeCheck,if_neg hi,Bool.and_eq_true,decide_eq_true_eq] using hc
    have hr := affineRangeCheck_sound hh.2 ht
    rw [ContinuousLayerCell.scorePoly_tail_eval hi,he]
    exact (StaticLow.tail_values hr.1).1.symm

/-- Interior free-piece slope semantics. Supporting ranks never use the tail
branch in the exported certificate, so no tail slope convention is required. -/
theorem profileRangeCheck_slope {i : ℕ} {a b : ℚ} (hi : i<242)
    (hc : profileRangeCheck i a b=true) {t : ℝ} (ht : t∈Ioo 0 1) :
    (ContinuousLayerCell.slopePoly i [a,b-a]).eval t=
      StaticLow.slope ((a:ℝ)+((b:ℝ)-a)*t) := by
  have he : RationalPolynomial.eval [a,b-a] t=(a:ℝ)+((b:ℝ)-a)*t := by
    simp [RationalPolynomial.eval]
    <;> ring
  have hr := affineRangeCheck_sound (show affineRangeCheck (profilePiece i).lo (profilePiece i).hi a b=true by
    simpa only [profileRangeCheck,if_pos hi] using hc) ht
  rw [ContinuousLayerCell.slopePoly_piece_eval hi,he]
  exact (StaticLow.piece_values hi hr).2.2.symm

end OptimalG.Certificates.StaticSupport
