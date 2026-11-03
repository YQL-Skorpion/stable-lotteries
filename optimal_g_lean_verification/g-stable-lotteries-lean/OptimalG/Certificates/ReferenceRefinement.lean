import OptimalG.Certificates.ReferenceFlowPartition
import OptimalG.Certificates.ReferenceFlowGeometry

/-! Exact affine subdivision preserves the actual reference field and cubic
value. Fine quadrature and flux cells therefore refer to the same flow as the
coarser residual certificate. -/
namespace OptimalG.Certificates.Transport
open Set
namespace ReferenceFlowCell

def interpolateNode (c : ReferenceFlowCell) (t : ℚ) : ReferenceNode :=
  ⟨c.segment.left.z+(c.segment.right.z-c.segment.left.z)*t,
   c.segment.left.r+(c.segment.right.r-c.segment.left.r)*t,
   c.segment.left.a+(c.segment.right.a-c.segment.left.a)*t⟩

def refinementCheck (parent child : ReferenceFlowCell) (lo hi : ℚ) : Bool :=
  decide (child.lam=parent.lam ∧ child.slack=parent.slack ∧ child.level=parent.level ∧
    child.late=parent.late ∧ child.rPiece=parent.rPiece ∧ child.aPiece=parent.aPiece ∧
    child.segment.left=parent.interpolateNode lo ∧ child.segment.right=parent.interpolateNode hi ∧
    0≤lo ∧ lo<hi ∧ hi≤1) &&
  child.valuePolynomial.eqCheck (parent.valuePolynomial.compose [lo,hi-lo])

theorem affine_subdivision (x y lo hi : ℚ) (t : ℝ) :
    (affineExpr (x+(y-x)*lo) (x+(y-x)*hi)).evalOne t=
      (affineExpr x y).evalOne ((lo:ℝ)+(hi-lo)*t) := by
  simp [affineExpr,RatExpr.evalOne,RatExpr.eval]
  ring

theorem refinementCheck_fields {parent child : ReferenceFlowCell} {lo hi : ℚ}
    (hc : refinementCheck parent child lo hi=true) (t : ℝ) :
    child.rankR.evalOne t=parent.rankR.evalOne ((lo:ℝ)+(hi-lo)*t) ∧
    child.rankA.evalOne t=parent.rankA.evalOne ((lo:ℝ)+(hi-lo)*t) ∧
    child.highRank.evalOne t=parent.highRank.evalOne ((lo:ℝ)+(hi-lo)*t) ∧
    child.actualAlpha t=parent.actualAlpha ((lo:ℝ)+(hi-lo)*t) ∧
    child.actualBeta t=parent.actualBeta ((lo:ℝ)+(hi-lo)*t) ∧
    child.valuePolynomial.eval t=parent.valuePolynomial.eval ((lo:ℝ)+(hi-lo)*t) := by
  obtain ⟨hg,hp⟩ := Bool.and_eq_true_iff.mp hc
  have h : child.lam=parent.lam ∧ child.slack=parent.slack ∧ child.level=parent.level ∧
      child.late=parent.late ∧ child.rPiece=parent.rPiece ∧ child.aPiece=parent.aPiece ∧
      child.segment.left=parent.interpolateNode lo ∧ child.segment.right=parent.interpolateNode hi ∧
      0≤lo ∧ lo<hi ∧ hi≤1 := of_decide_eq_true hg
  rcases h with ⟨hl,hs,hm,hb,hrp,hap,hlft,hrgt,_,_,_⟩
  have hr : child.rankR.evalOne t=parent.rankR.evalOne ((lo:ℝ)+(hi-lo)*t) := by
    simpa only [rankR,hlft,hrgt,interpolateNode] using
      affine_subdivision parent.segment.left.r parent.segment.right.r lo hi t
  have ha : child.rankA.evalOne t=parent.rankA.evalOne ((lo:ℝ)+(hi-lo)*t) := by
    simpa only [rankA,hlft,hrgt,interpolateNode] using
      affine_subdivision parent.segment.left.a parent.segment.right.a lo hi t
  have hz : child.highRank.evalOne t=parent.highRank.evalOne ((lo:ℝ)+(hi-lo)*t) := by
    simpa only [highRank,hlft,hrgt,interpolateNode] using
      affine_subdivision parent.segment.left.z parent.segment.right.z lo hi t
  refine ⟨hr,ha,hz,?_,?_,?_⟩
  · simp only [actualAlpha,hl,hs,hb,hrp,hap,hr,ha]
  · simp only [actualBeta,hl,hs,hm,hb,hrp,hap,hr,ha,hz]
  · have hh := RationalPolynomial.eqCheck_sound hp t
    simpa only [RationalPolynomial.eval_compose,RationalPolynomial.eval,Rat.cast_sub,
      mul_zero,add_zero,mul_comm] using hh

theorem refinementCheck_parameter {parent child : ReferenceFlowCell} {lo hi : ℚ}
    (hc : refinementCheck parent child lo hi=true) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (lo:ℝ)+(hi-lo)*t∈Icc (0:ℝ) 1 := by
  have h : child.lam=parent.lam ∧ child.slack=parent.slack ∧ child.level=parent.level ∧
      child.late=parent.late ∧ child.rPiece=parent.rPiece ∧ child.aPiece=parent.aPiece ∧
      child.segment.left=parent.interpolateNode lo ∧ child.segment.right=parent.interpolateNode hi ∧
      0≤lo ∧ lo<hi ∧ hi≤1 := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
  rcases h with ⟨_,_,_,_,_,_,_,_,hl,ho,hh⟩
  have hl' : (0:ℝ)≤lo := by exact_mod_cast hl
  have ho' : (lo:ℝ)<hi := by exact_mod_cast ho
  have hh' : (hi:ℝ)≤1 := by exact_mod_cast hh
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr ho'.le) ht.1,
    mul_nonneg (sub_nonneg.mpr ho'.le) (show 0≤1-t by linarith [ht.2])]

end ReferenceFlowCell
end OptimalG.Certificates.Transport
