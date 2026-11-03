import OptimalG.Certificates.ReferenceMatchedBranches
import OptimalG.Certificates.ReferenceSupportGeometry
import OptimalG.Certificates.ReferenceFlowAE

/-! The same finite time cover selects the matched ranks, their derivatives,
reference profiles and all four coefficients. Local support statements glue
to the actual early/late disjunction without a branch-selection assumption. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory Variational

theorem reference_matched_branches_ae {lam delta M : ℝ} {d : LowRankData}
    {G : ℝ→ℝ} {start finish : ℚ} {cells : List ReferenceFlowCell}
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    (hd : Admissible lam d) (hdelta : 0≤delta)
    (ref : ReferenceData) (hparam : (ref.lam:ℝ)=lam+delta)
    (hlow : ref.lowCurveCheck=true) (hgauge : ref.gaugeCheck=true)
    (ha : xLo≤ref.leftContact) (hb : (ref.rightContact:ℝ)≤pHi) (hG : Monotone G)
    (hmatch : ∀ r∈Icc (ref.leftContact:ℝ) ref.rightContact,
      G r∈Icc (ref.leftContact:ℝ) ref.rightContact ∧
      ParameterTransfer.shiftedPrimitive lam d delta (G r)=
        ref.transportPrimitive (ParameterTransfer.scalar d.S delta) r)
    (hgood : ∀ᵐ r ∂volume.restrict (Icc (ref.leftContact:ℝ) ref.rightContact),
      0<deriv G r ∧ d.phi (G r)=
        ref.transportScore (ParameterTransfer.scalar d.S delta) r/deriv G r ∧
      (G r,d.phi (G r))∈rankScoreSupport d.phi)
    (hcover : referenceFlowCoverCheck start finish cells=true)
    (hcells : ∀ f∈cells,∃ c : ReferenceScalarCell,∃ rb ab : ReferenceProfileBox,
      c.flow=f ∧ scalarFor f=c ∧
      (c.rProfile rb).frameCheck ref=true ∧ (c.aProfile ab).frameCheck ref=true ∧
      (c.flow.level:ℝ)=M ∧ c.start=start ∧ c.finish=finish ∧
      c.SupportGeometry ref.leftContact ref.rightContact) :
    ∀ᵐ s ∂volume.restrict (Icc (start:ℝ) finish),
      let S := ParameterTransfer.scalar d.S delta
      let r := referenceMatchedRank scalarFor cells true G s
      let a := referenceMatchedRank scalarFor cells false G s
      let R := referenceMappedProfile scalarFor cells true (ref.transportPrimitive S) s
      let mR := referenceMappedProfile scalarFor cells true (ref.transportScore S) s
      let mA := referenceMappedProfile scalarFor cells false (ref.transportScore S) s
      let xiR := referenceDerivative scalarFor cells true G s
      let xiA := referenceDerivative scalarFor cells false G s
      let coeff := fun i=>referenceMatchedCoefficient scalarFor cells S G i s
      (coeff=earlyLogCoefficients (lam+delta) M S
          (highWarp start finish (S-ref.slack) s) r a R
          (highWarpSlope start finish (S-ref.slack)) mA ∧
        ((r,a,a),mA/xiA,mA/xiA)∈controlFeatureSupport d ∧
        ParameterTransfer.shiftedPrimitive lam d delta r≤R) ∨
      (coeff=lateLogCoefficients (lam+delta) M S
          (highWarp start finish (S-ref.slack) s) r a R
          (highWarpSlope start finish (S-ref.slack)) mR mA ∧
        ((r,a,r),mA/xiA,mR/xiR)∈controlFeatureSupport d ∧
        ParameterTransfer.shiftedPrimitive lam d delta r=R) := by
  rw [←Measure.restrict_congr_set Ioc_ae_eq_Icc]
  apply referenceFlowCoverCheck_ae_Ioc hcover
  intro f hf
  obtain ⟨c,rb,ab,rfl,hscalar,hRframe,hAframe,hlevel,hstart,hfinish,hgeom⟩ := hcells f hf
  have htime := (referenceFlowCoverCheck_bounds hcover hf).2.1
  have hlocal := ReferenceScalarCell.matched_coefficient_branch_ae hd hdelta ref hparam
    hlow hgauge ha hb hG hmatch hgood c rb ab hRframe hAframe hlevel htime
    hgeom.r_order hgeom.a_order hgeom.a_present hgeom.late_r_present
    hgeom.central_r_range hgeom.cap_r_range hgeom.a_range hgeom.early_central_order
  rw [←Measure.restrict_congr_set Ioc_ae_eq_Icc] at hlocal
  filter_upwards [hlocal,ae_restrict_mem measurableSet_Ioc] with s hs hsi
  dsimp only at hs ⊢
  have heCoeff : (fun i=>referenceMatchedCoefficient scalarFor cells
      (ParameterTransfer.scalar d.S delta) G i s)=
      (fun i=>(c.params.coefficients c.flow.late i).eval
        (c.endpointChord (c.flow.timeParameter s) (fun _=>0)
          (ParameterTransfer.scalar d.S delta)
          (c.globalMatchedRank true G (c.flow.timeParameter s))
          (c.globalMatchedRank false G (c.flow.timeParameter s)))) := by
    funext i
    exact referenceMatchedCoefficient_on_cell scalarFor hcover hf hscalar _ G hsi _ i
  rw [heCoeff,
    referenceMatchedRank_on_cell scalarFor hcover hf hscalar true G hsi,
    referenceMatchedRank_on_cell scalarFor hcover hf hscalar false G hsi,
    referenceMappedProfile_on_cell scalarFor hcover hf hscalar true
      (ref.transportPrimitive (ParameterTransfer.scalar d.S delta)) hsi,
    referenceMappedProfile_on_cell scalarFor hcover hf hscalar true
      (ref.transportScore (ParameterTransfer.scalar d.S delta)) hsi,
    referenceMappedProfile_on_cell scalarFor hcover hf hscalar false
      (ref.transportScore (ParameterTransfer.scalar d.S delta)) hsi,
    referenceDerivative_on_cell scalarFor hcover hf hscalar true G hsi,
    referenceDerivative_on_cell scalarFor hcover hf hscalar false G hsi]
  simpa only [hstart,hfinish] using hs

end OptimalG.Certificates.Transport
