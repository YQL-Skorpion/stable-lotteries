import OptimalG.Certificates.ReferenceHessianFrame
import OptimalG.Certificates.ReferenceMatchedGlobal
import OptimalG.VariationalHighWarp

/-! The endpoint of a checked comparison chord evaluates to the same actual
early/late coefficients used by logarithmic transport. Frozen profile and
gauge coordinates stay at their reference ranks; only the matching ranks and
the scalar parameter change. -/
namespace OptimalG.Certificates.Transport.ReferenceScalarCell
open RatExpr Set

noncomputable def endpointChord (c : ReferenceScalarCell) (t : ℝ) (w : Fin 4→ℝ)
    (S r a : ℝ) : Fin 16→ℝ :=
  FrozenParameters.comparisonChord (c.weightedInput t w) (S-c.flow.slack)
    (r-c.weightedInput t w 1) (a-c.weightedInput t w 2) 1

theorem endpointChord_coordinates (c : ReferenceScalarCell) (t : ℝ) (w : Fin 4→ℝ)
    (S r a : ℝ) :
    c.endpointChord t w S r a 0=S ∧ c.endpointChord t w S r a 1=r ∧
    c.endpointChord t w S r a 2=a ∧
    ∀ (i : Fin 16), 3 ≤ i.val → i.val < 12 → c.endpointChord t w S r a i = c.frozenInput t i := by
  refine ⟨?_,?_,?_,?_⟩
  · change (c.flow.slack:ℝ)+1*(S-c.flow.slack)=S
    ring
  · change c.frozenInput t 1+1*(r-c.frozenInput t 1)=r
    ring
  · change c.frozenInput t 2+1*(a-c.frozenInput t 2)=a
    ring
  · intro i hi hlo
    fin_cases i <;> simp_all [endpointChord,FrozenParameters.comparisonChord,
      FrozenParameters.threeDirection,weightedInput]

theorem endpointChord_coefficient (c : ReferenceScalarCell) (t : ℝ) (w : Fin 4→ℝ)
    (S r a : ℝ) (i : Fin 4) :
    (c.params.coefficients c.flow.late i).eval (c.endpointChord t w S r a)=
      if c.flow.late then Variational.lateLogCoefficients c.flow.lam c.flow.level S
        (c.flow.highRank.evalOne t+(S-c.flow.slack)*c.warp.evalOne t) r a
        (c.flow.Rexpr.evalOne t+(S-c.flow.slack)*c.rGauge.evalOne t)
        (1+(S-c.flow.slack)*c.warpDerivative.evalOne t)
        (c.flow.scoreR.evalOne t+(S-c.flow.slack)*c.rGaugeDerivative.evalOne t)
        (c.flow.scoreA.evalOne t+(S-c.flow.slack)*c.aGaugeDerivative.evalOne t) i
      else Variational.earlyLogCoefficients c.flow.lam c.flow.level S
        (c.flow.highRank.evalOne t+(S-c.flow.slack)*c.warp.evalOne t) r a
        (c.flow.Rexpr.evalOne t+(S-c.flow.slack)*c.rGauge.evalOne t)
        (1+(S-c.flow.slack)*c.warpDerivative.evalOne t)
        (c.flow.scoreA.evalOne t+(S-c.flow.slack)*c.aGaugeDerivative.evalOne t) i := by
  obtain ⟨h0,h1,h2,hrest⟩ := c.endpointChord_coordinates t w S r a
  rw [FrozenParameters.coefficients_eval]
  simp only [FrozenParameters.referenceHighRank,FrozenParameters.referencePrimitive,
    FrozenParameters.jacobian,FrozenParameters.shiftedScoreR,FrozenParameters.shiftedScoreA,
    h0,h1,h2,hrest 3 (by norm_num) (by norm_num),hrest 4 (by norm_num) (by norm_num),
    hrest 5 (by norm_num) (by norm_num),hrest 6 (by norm_num) (by norm_num),
    hrest 7 (by norm_num) (by norm_num),hrest 8 (by norm_num) (by norm_num),
    hrest 9 (by norm_num) (by norm_num),hrest 10 (by norm_num) (by norm_num),
    hrest 11 (by norm_num) (by norm_num)]
  rfl

theorem endpointChord_time (c : ReferenceScalarCell) (t S : ℝ) :
    c.flow.highRank.evalOne t+(S-c.flow.slack)*c.warp.evalOne t=
      Variational.highWarp c.start c.finish (S-c.flow.slack) (c.flow.highRank.evalOne t) ∧
    1+(S-c.flow.slack)*c.warpDerivative.evalOne t=
      Variational.highWarpSlope c.start c.finish (S-c.flow.slack) := by
  simp only [warp,warpDerivative,evalOne,eval_mulNotation,eval_subNotation,eval,
    Rat.cast_div,Rat.cast_neg,Rat.cast_one,Rat.cast_sub,
    Variational.highWarp,Variational.highWarpSlope]
  constructor <;> ring

/-- Exact profile frames identify the frozen scalar-warped primitive and
both score coordinates with the single global reference curve. -/
theorem endpointChord_global_profiles (ref : ReferenceData)
    (hlow : ref.lowCurveCheck=true) (hgauge : ref.gaugeCheck=true)
    (c : ReferenceScalarCell) (rb ab : ReferenceProfileBox)
    (hR : (c.rProfile rb).frameCheck ref=true)
    (hA : (c.aProfile ab).frameCheck ref=true)
    (hrorder : c.flow.segment.left.r≤c.flow.segment.right.r)
    (haorder : c.flow.segment.left.a≤c.flow.segment.right.a)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (S : ℝ) :
    c.flow.Rexpr.evalOne t+(S-c.flow.slack)*c.rGauge.evalOne t=
      ref.transportPrimitive S (c.referenceRank true t) ∧
    c.flow.scoreR.evalOne t+(S-c.flow.slack)*c.rGaugeDerivative.evalOne t=
      ref.transportScore S (c.referenceRank true t) ∧
    c.flow.scoreA.evalOne t+(S-c.flow.slack)*c.aGaugeDerivative.evalOne t=
      ref.transportScore S (c.referenceRank false t) := by
  have hr := ReferenceFlowCell.affineExpr_mem hrorder ht
  change c.flow.rankR.evalOne t ∈ Icc (c.flow.segment.left.r:ℝ) c.flow.segment.right.r at hr
  have ha := ReferenceFlowCell.affineExpr_mem haorder ht
  change c.flow.rankA.evalOne t ∈ Icc (c.flow.segment.left.a:ℝ) c.flow.segment.right.a at ha
  have hvr := ReferenceProfileCell.frameCheck_values ref hlow hgauge (c.rProfile rb) hR hr
  have hva := ReferenceProfileCell.frameCheck_values ref hlow hgauge (c.aProfile ab) hA ha
  have hs : c.flow.slack=ref.slack :=
    (of_decide_eq_true (Bool.and_eq_true_iff.mp hR).1).2.1
  have hgr := c.rProfile_gauge rb t
  have hga := c.aProfile_gauge_derivative ab t
  simp only [ReferenceData.transportPrimitive,ReferenceData.transportScore,referenceRank,
    Bool.false_eq_true,if_true,if_false]
  rw [←hvr.2.1,←hvr.1,←hva.1,←hvr.2.2.1,←hvr.2.2.2,←hva.2.2.2,←hs]
  rw [hgr.1,hgr.2,hga]
  simp [ReferenceFlowCell.Rexpr,ReferenceFlowCell.scoreR,ReferenceFlowCell.scoreA,evalOne,
    ReferenceFlowCell.primitiveExpr_eval,ReferenceFlowCell.scoreExpr_eval,rProfile,aProfile]

end OptimalG.Certificates.Transport.ReferenceScalarCell
