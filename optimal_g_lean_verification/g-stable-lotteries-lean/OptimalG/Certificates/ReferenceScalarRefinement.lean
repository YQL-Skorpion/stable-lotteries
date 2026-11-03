import OptimalG.Certificates.ReferenceRefinement
import OptimalG.Certificates.ReferenceFrozenProfiles

/-! Refined scalar and positional cells use exactly the same frozen inputs
and coordinate derivatives as their coarse reference cell. No new reference
flow or first-variation function is introduced by subdivision. -/
namespace OptimalG.Certificates.Transport.ReferenceScalarCell
open RatExpr

/-- The metadata unchanged by a subdivision, exposed as a Boolean finite check. -/
def refinementMetadataCheck (parent child : ReferenceScalarCell) : Bool :=
  decide (child.leftContact=parent.leftContact ∧ child.rightContact=parent.rightContact ∧
    child.start=parent.start ∧ child.finish=parent.finish ∧ child.gauge=parent.gauge ∧
    child.gaugeDerivative=parent.gaugeDerivative)

theorem refinementCheck_sources {parent child : ReferenceScalarCell} {lo hi : ℚ}
    (hflow : parent.flow.refinementCheck child.flow lo hi=true) :
    child.params=parent.params ∧ child.alphaSource=parent.alphaSource ∧
      child.betaSource=parent.betaSource := by
  have h := of_decide_eq_true (Bool.and_eq_true_iff.mp hflow).1
  have hL : child.flow.lam=parent.flow.lam := h.1
  have hS : child.flow.slack=parent.flow.slack := h.2.1
  have hM : child.flow.level=parent.flow.level := h.2.2.1
  have hbranch : child.flow.late=parent.flow.late := h.2.2.2.1
  simp only [params,alphaSource,betaSource,hL,hS,hM,hbranch,and_self]

theorem refinementCheck_frozenInput {parent child : ReferenceScalarCell} {lo hi : ℚ}
    (hflow : parent.flow.refinementCheck child.flow lo hi=true)
    (hmeta : refinementMetadataCheck parent child=true) (t : ℝ) :
    child.frozenInput t=parent.frozenInput ((lo:ℝ)+(hi-lo)*t) := by
  let tau : ℝ := (lo:ℝ)+(hi-lo)*t
  have h := of_decide_eq_true (Bool.and_eq_true_iff.mp hflow).1
  have hL : child.flow.lam=parent.flow.lam := h.1
  have hS : child.flow.slack=parent.flow.slack := h.2.1
  have hRpiece : child.flow.rPiece=parent.flow.rPiece := h.2.2.2.2.1
  have hApiece : child.flow.aPiece=parent.flow.aPiece := h.2.2.2.2.2.1
  obtain ⟨hleft,hright,hstart,hfinish,hg,hgd⟩ := of_decide_eq_true hmeta
  obtain ⟨hr,ha,hz,_,_,_⟩ := ReferenceFlowCell.refinementCheck_fields hflow t
  change child.flow.rankR.evalOne t=parent.flow.rankR.evalOne tau at hr
  change child.flow.rankA.evalOne t=parent.flow.rankA.evalOne tau at ha
  change child.flow.highRank.evalOne t=parent.flow.highRank.evalOne tau at hz
  have hprim : child.flow.Rexpr.evalOne t=parent.flow.Rexpr.evalOne tau := by
    simp only [ReferenceFlowCell.Rexpr,evalOne,ReferenceFlowCell.primitiveExpr_eval]
    change ReferenceFlowCell.localPrimitive child.flow.lam child.flow.slack child.flow.rPiece
      (child.flow.rankR.evalOne t)=_
    rw [hL,hS,hRpiece,hr]
    rfl
  have hscoreR : child.flow.scoreR.evalOne t=parent.flow.scoreR.evalOne tau := by
    simp only [ReferenceFlowCell.scoreR,evalOne,ReferenceFlowCell.scoreExpr_eval]
    change ReferenceFlowCell.localScore child.flow.lam child.flow.slack child.flow.rPiece
      (child.flow.rankR.evalOne t)=_
    rw [hL,hS,hRpiece,hr]
    rfl
  have hscoreA : child.flow.scoreA.evalOne t=parent.flow.scoreA.evalOne tau := by
    simp only [ReferenceFlowCell.scoreA,evalOne,ReferenceFlowCell.scoreExpr_eval]
    change ReferenceFlowCell.localScore child.flow.lam child.flow.slack child.flow.aPiece
      (child.flow.rankA.evalOne t)=_
    rw [hL,hS,hApiece,ha]
    rfl
  -- These gauge identities do not inspect any profile enclosure.
  let box : ReferenceProfileBox := ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩
  have hGauge : child.rGauge.evalOne t=parent.rGauge.evalOne tau := by
    rw [←(child.rProfile_gauge box t).1,←(parent.rProfile_gauge box tau).1]
    simp only [rProfile,ReferenceProfileCell.localGauge,hL,hleft,hright,hg,hRpiece,hr]
  have hGaugeR : child.rGaugeDerivative.evalOne t=parent.rGaugeDerivative.evalOne tau := by
    rw [←(child.rProfile_gauge box t).2,←(parent.rProfile_gauge box tau).2]
    simp only [rProfile,ReferenceProfileCell.localGaugeDerivative,hL,hleft,hright,hgd,hRpiece,hr]
  have hGaugeA : child.aGaugeDerivative.evalOne t=parent.aGaugeDerivative.evalOne tau := by
    rw [←child.aProfile_gauge_derivative box t,←parent.aProfile_gauge_derivative box tau]
    simp only [aProfile,ReferenceProfileCell.localGaugeDerivative,hL,hleft,hright,hgd,hApiece,ha]
  have hWarpD : child.warpDerivative.evalOne t=parent.warpDerivative.evalOne tau := by
    simp only [warpDerivative,evalOne,eval,hstart,hfinish]
  have hWarp : child.warp.evalOne t=parent.warp.evalOne tau := by
    change child.warpDerivative.evalOne t*(child.flow.highRank.evalOne t-child.start)=
      parent.warpDerivative.evalOne tau*(parent.flow.highRank.evalOne tau-parent.start)
    rw [hWarpD,hz,hstart]
  change child.frozenInput t=parent.frozenInput tau
  funext i
  fin_cases i <;>
    simp [frozenInput,frozenSubstitution,Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals first
    | exact hr
    | exact ha
    | exact hz
    | exact hprim
    | exact hscoreR
    | exact hscoreA
    | exact hGauge
    | exact hGaugeR
    | exact hGaugeA
    | exact hWarp
    | exact hWarpD
    | simp only [evalOne,eval,hS]

theorem refinementCheck_coordinate_forces {parent child : ReferenceScalarCell} {lo hi : ℚ}
    (hflow : parent.flow.refinementCheck child.flow lo hi=true)
    (hmeta : refinementMetadataCheck parent child=true) (t : ℝ) (j : Fin 16) :
    (partialExpr j child.alphaSource).eval (child.frozenInput t)=
      (partialExpr j parent.alphaSource).eval (parent.frozenInput ((lo:ℝ)+(hi-lo)*t)) ∧
    (partialExpr j child.betaSource).eval (child.frozenInput t)=
      (partialExpr j parent.betaSource).eval (parent.frozenInput ((lo:ℝ)+(hi-lo)*t)) := by
  have hs := refinementCheck_sources hflow
  rw [hs.2.1,hs.2.2,refinementCheck_frozenInput hflow hmeta t]
  exact ⟨rfl,rfl⟩

theorem refinementCheck_scalar_forces {parent child : ReferenceScalarCell} {lo hi : ℚ}
    (hflow : parent.flow.refinementCheck child.flow lo hi=true)
    (hmeta : refinementMetadataCheck parent child=true) (t : ℝ) :
    child.actualAlphaS t=parent.actualAlphaS ((lo:ℝ)+(hi-lo)*t) ∧
      child.actualBetaS t=parent.actualBetaS ((lo:ℝ)+(hi-lo)*t) :=
  refinementCheck_coordinate_forces hflow hmeta t 0

end OptimalG.Certificates.Transport.ReferenceScalarCell
