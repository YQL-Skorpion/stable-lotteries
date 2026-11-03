import OptimalG.Certificates.ReferenceGlobalBranches
import OptimalG.Certificates.ReferenceTransferredFlow
import OptimalG.Certificates.ReferenceFlowBoundaryData.CoarseLowerShape
import OptimalG.Certificates.ReferenceCoefficientPairData.CoarseLowerShape
namespace OptimalG.Certificates.ReferenceFlowData.CoarseLowerShape
open Set MeasureTheory Transport Variational ParameterTransfer
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem support_cells : ∀ f∈ReferenceActualData.CoarseLowerShape.cells,∃ c rb ab,c.flow=f ∧ ReferenceSensitivityData.CoarseLowerShape.makeCell f=c ∧
    (c.rProfile rb).frameCheck TransportReferenceData.CoarseLowerShape.data=true ∧ (c.aProfile ab).frameCheck TransportReferenceData.CoarseLowerShape.data=true ∧
    (c.flow.level:ℝ)=(0.135:ℝ) ∧ c.start=ReferenceActualData.CoarseLowerShape.start ∧ c.finish=ReferenceActualData.CoarseLowerShape.finish ∧
    c.SupportGeometry TransportReferenceData.CoarseLowerShape.data.leftContact TransportReferenceData.CoarseLowerShape.data.rightContact := by
  intro f hf
  rw [←ReferenceTimeData.CoarseLowerShape.Assembly.source_cells] at hf
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hf
  obtain ⟨rb,hr,_⟩ := ReferenceTimeData.CoarseLowerShape.Assembly.source_rank_frames p hp true
  obtain ⟨ab,ha,_⟩ := ReferenceTimeData.CoarseLowerShape.Assembly.source_rank_frames p hp false
  refine ⟨p.1,rb,ab,rfl,ReferenceTimeData.CoarseLowerShape.Assembly.source_scalar p hp,hr,ha,?_,?_,?_,ReferenceTimeData.CoarseLowerShape.Assembly.source_support_geometry hp⟩
  · have hlevel : p.1.flow.level=TransportHessianData.CoarseLowerShapeFlow.params.level := congrArg FrozenParameters.level (ReferenceTimeData.CoarseLowerShape.Assembly.source_geometry p hp).1
    rw [hlevel]
    norm_num [TransportHessianData.CoarseLowerShapeFlow.params]
  · rw [←ReferenceTimeData.CoarseLowerShape.Assembly.source_scalar p hp]
    rfl
  · rw [←ReferenceTimeData.CoarseLowerShape.Assembly.source_scalar p hp]
    rfl

theorem actual_flow {lam delta : ℝ} {d : LowRankData} {oldY : ℝ→ℝ}
    (hd : Admissible lam d) (hdelta : 0≤delta) (hparam : (TransportReferenceData.CoarseLowerShape.data.lam:ℝ)=lam+delta)
    (transfer : UpwardTransfer lam delta d oldY) (G : StieltjesFunction ℝ)
    (hmatch : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right ∧
      shiftedPrimitive lam d delta (G r)=TransportReferenceData.CoarseLowerShape.data.transportPrimitive (scalar d.S delta) r)
    (hgood : ∀ᵐ r ∂volume.restrict (Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right),HasDerivAt G (deriv G r) r ∧
      0<deriv G r ∧ (3/5:ℝ)≤deriv G r ∧
      d.phi (G r)=TransportReferenceData.CoarseLowerShape.data.transportScore (scalar d.S delta) r/deriv G r ∧
      (G r,d.phi (G r))∈rankScoreSupport d.phi) :
    ReferenceCompetitorData.CoarseLowerShape.initial transfer+ReferenceCoercivityData.CoarseLowerShape.flow (scalar d.S delta) G-ReferenceCoercivityData.CoarseLowerShape.derivativeFlux G+ReferenceCoercivityData.CoarseLowerShape.entropyFlux G≤
      ReferenceFlowBoundaryData.CoarseLowerShape.terminalLog transfer-Real.log (ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish) := by
  have hL := ReferenceCompetitorData.CoarseLowerShape.parameter_range hparam
  have hS := ReferenceCompetitorData.CoarseLowerShape.scalar_range hd hdelta hparam
  have hobstacle := ReferenceCompetitorData.CoarseLowerShape.shifted_obstacles hd hdelta hparam
  have hderivG : ∀ᵐ r ∂volume.restrict (Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right),(3/5:ℝ)≤deriv G r :=
    hgood.mono (fun r hr=>hr.2.2.1)
  have hbranch := reference_matched_branches_ae (M:=0.135) ReferenceSensitivityData.CoarseLowerShape.makeCell hd hdelta TransportReferenceData.CoarseLowerShape.data hparam
    ReferenceLowData.CoarseLowerShape.checked TransportReferenceData.CoarseLowerShape.gauge_checked
    (by norm_num [xLo,TransportReferenceData.CoarseLowerShape.data,TransportReferenceData.CoarseLowerShape.leftContact])
    (by norm_num [pHi,TransportReferenceData.CoarseLowerShape.data,TransportReferenceData.CoarseLowerShape.rightContact]) G.mono hmatch
    (hgood.mono (fun r hr=>⟨hr.2.1,hr.2.2.2.1,hr.2.2.2.2⟩)) ReferenceActualData.CoarseLowerShape.cover_checked support_cells
  have hpairs := ReferenceCoefficientPairData.CoarseLowerShape.paired_ae hS G hobstacle hmatch
  have hxi := ReferenceDerivativeWitnessData.CoarseLowerShape.xi_positive G hderivG
  have hpositive : ∀ᵐ z ∂volume.restrict (Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish),∀ i,
      ((ReferenceTaylorData.CoarseLowerShape.coefficient (scalar d.S delta) G i z=0 ∧ referenceCoefficient ReferenceActualData.CoarseLowerShape.cells i z=0) ∨
        (0<ReferenceTaylorData.CoarseLowerShape.coefficient (scalar d.S delta) G i z ∧ 0<referenceCoefficient ReferenceActualData.CoarseLowerShape.cells i z)) ∧
        0<transportXi (ReferenceDerivativeWitnessData.CoarseLowerShape.derivative true G z) (ReferenceDerivativeWitnessData.CoarseLowerShape.derivative false G z) i := by
    filter_upwards [hpairs,hxi] with z hp hxi
    exact fun i=>⟨hp i,hxi i⟩
  have hD := ReferenceDerivativeWitnessData.CoarseLowerShape.actual_derivative_source G
  have hE := ReferenceDerivativeWitnessData.CoarseLowerShape.actual_entropy_source G hderivG
  have hh := transferred_reference_flow hd hL hdelta transfer
    ReferenceFlowBoundaryData.CoarseLowerShape.start_geometry ReferenceFlowBoundaryData.CoarseLowerShape.finish_geometry ReferenceFlowBoundaryData.CoarseLowerShape.scalar_geometry ReferenceActualData.CoarseLowerShape.cover_checked
    ReferenceAdjointData.CoarseLowerShape.Z_spec.2.1 ReferenceAdjointData.CoarseLowerShape.Z_spec.2.2.2.2 ReferenceAdjointData.CoarseLowerShape.Z_spec.2.2.1 ReferenceActualData.CoarseLowerShape.beta_intervalIntegrable
    (fun z hz=>rfl) hbranch hpositive (ReferenceTaylorData.CoarseLowerShape.source_integrable hS G hobstacle hmatch) hD.1 hE.1
  change ReferenceAdjointData.CoarseLowerShape.rho ReferenceActualData.CoarseLowerShape.start*(logDeficit 0.135 (scalar d.S delta) transfer.trajectory
      (highWarp ReferenceActualData.CoarseLowerShape.start ReferenceActualData.CoarseLowerShape.finish (scalar d.S delta-TransportReferenceData.CoarseLowerShape.data.slack)) ReferenceActualData.CoarseLowerShape.start-
      Real.log (ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.start))+ReferenceCoercivityData.CoarseLowerShape.flow (scalar d.S delta) G-
    (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,transportDerivativeSource ReferenceAdjointData.CoarseLowerShape.rho (fun z=>Real.log (ReferenceAdjointData.CoarseLowerShape.Z z))
      (fun z i=>ReferenceAdjointData.CoarseLowerShape.coefficient i z) (ReferenceDerivativeWitnessData.CoarseLowerShape.xi G) transportDelta z)+
    (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,transportEntropySource ReferenceAdjointData.CoarseLowerShape.rho (fun z=>Real.log (ReferenceAdjointData.CoarseLowerShape.Z z))
      (fun z i=>ReferenceAdjointData.CoarseLowerShape.coefficient i z) (ReferenceDerivativeWitnessData.CoarseLowerShape.xi G) transportDelta z)≤
      ReferenceFlowBoundaryData.CoarseLowerShape.terminalLog transfer-Real.log (ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish) at hh
  rw [ReferenceFlowBoundaryData.CoarseLowerShape.actual_initial_gap hparam transfer,hD.2,hE.2] at hh
  exact hh

theorem no_actual_transfer {lam delta : ℝ} {d : LowRankData} {oldY : ℝ→ℝ}
    (hd : Admissible lam d) (hparam : (TransportReferenceData.CoarseLowerShape.data.lam:ℝ)=lam+delta)
    (hdelta : 0≤delta) (transfer : UpwardTransfer lam delta d oldY) : False := by
  obtain ⟨G,hleft,hmatch,hgood,hsq⟩ := ReferenceDisplacementData.CoarseLowerShape.actual_matching_exists hd hdelta hparam
  exact ReferenceCompetitorData.CoarseLowerShape.excludes_of_log_flow hd hparam hdelta transfer G hleft hmatch hsq
    (hgood.mono (fun r hr=>hr.2.2.1)) (actual_flow hd hdelta hparam transfer G hmatch hgood)
    (ReferenceFlowBoundaryData.CoarseLowerShape.actual_terminal_feasibility hd hdelta hparam transfer)

theorem lower_endpoint_not_feasible : ¬Feasible (TransportReferenceData.CoarseLowerShape.data.lam:ℝ) := by
  rintro ⟨d,hd,oldY,hY,hpass⟩
  have hp : (TransportReferenceData.CoarseLowerShape.data.lam:ℝ)=(TransportReferenceData.CoarseLowerShape.data.lam:ℝ)+0 := by ring
  obtain ⟨transfer⟩ := exists_upwardTransfer hd (ReferenceCompetitorData.CoarseLowerShape.parameter_range hp) (by norm_num) hY hpass
  exact no_actual_transfer hd hp (by norm_num) transfer
end OptimalG.Certificates.ReferenceFlowData.CoarseLowerShape
