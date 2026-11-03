import OptimalG.Certificates.ReferenceMatchedCoefficients
import OptimalG.Certificates.ReferenceMatchedControl

/-! All fields in the actual logarithmic comparison are selected by the
same coarse time partition. The coefficient identity below connects the
finite Hessian chord to the exact early/late control formulas. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory Variational

theorem ReferenceData.transportPrimitive_cap (ref : ReferenceData) (S : ℝ) {r : ℝ}
    (hr : r≤ref.leftContact) : ref.transportPrimitive S r=cap ref.lam S r :=
  warpedReference_cap hr (ref.lowPrimitive_cap hr)

noncomputable def referenceMatchedRank
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell) (cells : List ReferenceFlowCell)
    (useR : Bool) (G : ℝ→ℝ) : ℝ→ℝ :=
  referenceField (fun c=>(scalarFor c).globalMatchedRank useR G) cells

noncomputable def referenceMappedProfile
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell) (cells : List ReferenceFlowCell)
    (useR : Bool) (profile : ℝ→ℝ) : ℝ→ℝ :=
  referenceField (fun c t=>profile ((scalarFor c).referenceRank useR t)) cells

theorem ReferenceFlowCell.highRank_timeParameter (c : ReferenceFlowCell)
    (hpos : c.segment.left.z<c.segment.right.z) (z : ℝ) :
    c.highRank.evalOne (c.timeParameter z)=z := by
  have hne : (c.segment.right.z:ℝ)-c.segment.left.z≠0 := by
    exact_mod_cast (sub_ne_zero.mpr hpos.ne')
  simp only [ReferenceFlowCell.highRank,ReferenceFlowCell.affineExpr,
    ReferenceFlowCell.timeParameter,ReferenceFlowCell.length,RatExpr.evalOne,
    RatExpr.eval_addNotation,RatExpr.eval_mulNotation,RatExpr.eval,Rat.cast_sub]
  field_simp [hne]
  <;> ring

theorem referenceMatchedRank_on_cell
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    {start finish : ℚ} {cells : List ReferenceFlowCell} {c : ReferenceScalarCell}
    (hc : referenceFlowCoverCheck start finish cells=true) (hm : c.flow∈cells)
    (hcell : scalarFor c.flow=c) (useR : Bool) (G : ℝ→ℝ) {z : ℝ}
    (hz : z∈Ioc (c.flow.segment.left.z:ℝ) c.flow.segment.right.z) :
    referenceMatchedRank scalarFor cells useR G z=
      c.globalMatchedRank useR G (c.flow.timeParameter z) := by
  rw [referenceMatchedRank,referenceField_on_cell _ hc hm hz,hcell]

theorem referenceMappedProfile_on_cell
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    {start finish : ℚ} {cells : List ReferenceFlowCell} {c : ReferenceScalarCell}
    (hc : referenceFlowCoverCheck start finish cells=true) (hm : c.flow∈cells)
    (hcell : scalarFor c.flow=c) (useR : Bool) (profile : ℝ→ℝ) {z : ℝ}
    (hz : z∈Ioc (c.flow.segment.left.z:ℝ) c.flow.segment.right.z) :
    referenceMappedProfile scalarFor cells useR profile z=
      profile (c.referenceRank useR (c.flow.timeParameter z)) := by
  rw [referenceMappedProfile,referenceField_on_cell _ hc hm hz,hcell]

theorem referenceDerivative_on_cell
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    {start finish : ℚ} {cells : List ReferenceFlowCell} {c : ReferenceScalarCell}
    (hc : referenceFlowCoverCheck start finish cells=true) (hm : c.flow∈cells)
    (hcell : scalarFor c.flow=c) (useR : Bool) (G : ℝ→ℝ) {z : ℝ}
    (hz : z∈Ioc (c.flow.segment.left.z:ℝ) c.flow.segment.right.z) :
    referenceDerivative scalarFor cells useR G z=
      c.matchedDerivative useR G (c.flow.timeParameter z) := by
  rw [referenceDerivative,referenceField_on_cell _ hc hm hz,hcell]

theorem referenceMatchedCoefficient_control_formula
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    (ref : ReferenceData) (hlow : ref.lowCurveCheck=true) (hgauge : ref.gaugeCheck=true)
    {start finish : ℚ} {cells : List ReferenceFlowCell} {c : ReferenceScalarCell}
    (hc : referenceFlowCoverCheck start finish cells=true) (hm : c.flow∈cells)
    (hcell : scalarFor c.flow=c) (rb ab : ReferenceProfileBox)
    (hRframe : (c.rProfile rb).frameCheck ref=true)
    (hAframe : (c.aProfile ab).frameCheck ref=true)
    (hR : c.flow.segment.left.r≤c.flow.segment.right.r)
    (hA : c.flow.segment.left.a≤c.flow.segment.right.a)
    (hstart : c.start=start) (hfinish : c.finish=finish)
    (S : ℝ) (G : ℝ→ℝ) {z : ℝ}
    (hz : z∈Ioc (c.flow.segment.left.z:ℝ) c.flow.segment.right.z) (i : Fin 4) :
    referenceMatchedCoefficient scalarFor cells S G i z=
      if c.flow.late then lateLogCoefficients ref.lam c.flow.level S
        (highWarp start finish (S-ref.slack) z)
        (referenceMatchedRank scalarFor cells true G z)
        (referenceMatchedRank scalarFor cells false G z)
        (referenceMappedProfile scalarFor cells true (ref.transportPrimitive S) z)
        (highWarpSlope start finish (S-ref.slack))
        (referenceMappedProfile scalarFor cells true (ref.transportScore S) z)
        (referenceMappedProfile scalarFor cells false (ref.transportScore S) z) i
      else earlyLogCoefficients ref.lam c.flow.level S
        (highWarp start finish (S-ref.slack) z)
        (referenceMatchedRank scalarFor cells true G z)
        (referenceMatchedRank scalarFor cells false G z)
        (referenceMappedProfile scalarFor cells true (ref.transportPrimitive S) z)
        (highWarpSlope start finish (S-ref.slack))
        (referenceMappedProfile scalarFor cells false (ref.transportScore S) z) i := by
  have htime := (referenceFlowCoverCheck_bounds hc hm).2.1
  have ht := c.flow.timeParameter_mem htime ⟨hz.1.le,hz.2⟩
  have hp := ReferenceScalarCell.endpointChord_global_profiles ref hlow hgauge c rb ab hRframe hAframe
    hR hA ht S
  have hwarp := c.endpointChord_time (c.flow.timeParameter z) S
  have hmeta := of_decide_eq_true (Bool.and_eq_true_iff.mp hRframe).1
  have hL : c.flow.lam=ref.lam := hmeta.1
  have hS : c.flow.slack=ref.slack := hmeta.2.1
  rw [referenceMatchedCoefficient_on_cell scalarFor hc hm hcell S G hz (fun _=>0) i,
    c.endpointChord_coefficient,hwarp.1,hwarp.2,hp.1,hp.2.1,hp.2.2,
    c.flow.highRank_timeParameter htime z,hstart,hfinish,hL,hS]
  rw [referenceMatchedRank_on_cell scalarFor hc hm hcell true G hz,
    referenceMatchedRank_on_cell scalarFor hc hm hcell false G hz,
    referenceMappedProfile_on_cell scalarFor hc hm hcell true (ref.transportPrimitive S) hz,
    referenceMappedProfile_on_cell scalarFor hc hm hcell true (ref.transportScore S) hz,
    referenceMappedProfile_on_cell scalarFor hc hm hcell false (ref.transportScore S) hz]

end OptimalG.Certificates.Transport
