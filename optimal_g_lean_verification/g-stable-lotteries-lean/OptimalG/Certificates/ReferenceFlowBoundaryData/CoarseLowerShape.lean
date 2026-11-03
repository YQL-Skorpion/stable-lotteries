import OptimalG.Certificates.ReferenceCompetitorData.CoarseLowerShape
import OptimalG.VariationalHighWarp
import OptimalG.VariationalTransferredTerminal
namespace OptimalG.Certificates.ReferenceFlowBoundaryData.CoarseLowerShape
open Set MeasureTheory Transport Variational ParameterTransfer
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem start_geometry : (ReferenceActualData.CoarseLowerShape.start:ℝ)∈Icc (0.783:ℝ) 0.784 := by norm_num [ReferenceActualData.CoarseLowerShape.start]
theorem finish_geometry : (ReferenceActualData.CoarseLowerShape.finish:ℝ)∈Icc (0.862:ℝ) 0.863 := by norm_num [ReferenceActualData.CoarseLowerShape.finish]
theorem scalar_geometry : (TransportReferenceData.CoarseLowerShape.data.slack:ℝ)∈Icc (0.023:ℝ) 0.024 := by norm_num [TransportReferenceData.CoarseLowerShape.data,TransportReferenceData.CoarseLowerShape.slack]
theorem time_order : (ReferenceActualData.CoarseLowerShape.start:ℝ)<ReferenceActualData.CoarseLowerShape.finish := by norm_num [ReferenceActualData.CoarseLowerShape.start,ReferenceActualData.CoarseLowerShape.finish]
theorem initial_quadratic : ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.start=(0.135:ℝ)-quadratic TransportReferenceData.CoarseLowerShape.data.lam ReferenceActualData.CoarseLowerShape.start := by
  rw [ReferenceAdjointData.CoarseLowerShape.initial_value]
  norm_num [ReferenceInitialAdjointData.CoarseLowerShape.initial,TransportReferenceData.CoarseLowerShape.data,TransportReferenceData.CoarseLowerShape.lam,ReferenceActualData.CoarseLowerShape.start,quadratic]
noncomputable def terminalLog {lam delta : ℝ} {d : LowRankData} {Y : ℝ→ℝ}
    (T : UpwardTransfer lam delta d Y) : ℝ :=
  logDeficit 0.135 (scalar d.S delta) T.trajectory
    (highWarp ReferenceActualData.CoarseLowerShape.start ReferenceActualData.CoarseLowerShape.finish (scalar d.S delta-TransportReferenceData.CoarseLowerShape.data.slack)) ReferenceActualData.CoarseLowerShape.finish

theorem actual_initial_gap {lam delta : ℝ} {d : LowRankData} {Y : ℝ→ℝ}
    (hparam : (TransportReferenceData.CoarseLowerShape.data.lam:ℝ)=lam+delta) (T : UpwardTransfer lam delta d Y) :
    ReferenceAdjointData.CoarseLowerShape.rho ReferenceActualData.CoarseLowerShape.start*(logDeficit 0.135 (scalar d.S delta) T.trajectory
      (highWarp ReferenceActualData.CoarseLowerShape.start ReferenceActualData.CoarseLowerShape.finish (scalar d.S delta-TransportReferenceData.CoarseLowerShape.data.slack)) ReferenceActualData.CoarseLowerShape.start-
      Real.log (ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.start))=ReferenceCompetitorData.CoarseLowerShape.initial T := by
  have hz : quadratic (lam+delta) ReferenceActualData.CoarseLowerShape.start<(0.135:ℝ) := by
    rw [←hparam]
    have hpos := ReferenceAdjointData.CoarseLowerShape.initial_positive
    rw [initial_quadratic] at hpos
    linarith only [hpos]
  have hh := transferred_highWarp_initial_gap (M:=0.135) (b:=(ReferenceActualData.CoarseLowerShape.finish:ℝ))
    (ds:=scalar d.S delta-TransportReferenceData.CoarseLowerShape.data.slack) T
    (by norm_num [ReferenceActualData.CoarseLowerShape.start,zStart,zEnd]) hz
  have hinit : ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.start=(0.135:ℝ)-Variational.quadratic TransportReferenceData.CoarseLowerShape.data.lam ReferenceActualData.CoarseLowerShape.start := initial_quadratic
  rw [←hparam,←hinit] at hh
  rw [hh]
  rfl

theorem actual_terminal_feasibility {lam delta : ℝ} {d : LowRankData} {Y : ℝ→ℝ}
    (hd : Admissible lam d) (hdelta : 0≤delta) (hparam : (TransportReferenceData.CoarseLowerShape.data.lam:ℝ)=lam+delta)
    (T : UpwardTransfer lam delta d Y) :
    terminalLog T≤Real.log (ReferenceEndpointData.CoarseLowerShape.parameters.terminalDeficit (scalar d.S delta)) := by
  have hreg := transferred_reference_log_regular hd (ReferenceCompetitorData.CoarseLowerShape.parameter_range hparam) hdelta T
    start_geometry finish_geometry scalar_geometry
  have hpos := hreg.2.1 ReferenceActualData.CoarseLowerShape.finish ⟨time_order.le,le_rfl⟩
  rw [highWarp_terminal time_order] at hpos
  have hp : (ReferenceEndpointData.CoarseLowerShape.parameters.lam:ℝ)=lam+delta := hparam
  have hlevel : (ReferenceEndpointData.CoarseLowerShape.parameters.level:ℝ)=(0.135:ℝ) := by norm_num [ReferenceEndpointData.CoarseLowerShape.parameters]
  have hhigh : (ReferenceEndpointData.CoarseLowerShape.parameters.highRank:ℝ)=ReferenceActualData.CoarseLowerShape.finish := rfl
  have hslack : (ReferenceEndpointData.CoarseLowerShape.parameters.slack:ℝ)=TransportReferenceData.CoarseLowerShape.data.slack := rfl
  have hh := transferred_terminal_certificate_feasibility T hd (ReferenceCompetitorData.CoarseLowerShape.parameter_range hparam) hdelta
    ReferenceEndpointData.CoarseLowerShape.parameters hp
    (by simpa only [hhigh,hslack] using hreg.2.2)
    (by norm_num [ReferenceEndpointData.CoarseLowerShape.parameters,qLo,qHi])
    (by simpa only [hlevel,hhigh,hslack] using hpos)
  unfold terminalLog logDeficit
  rw [highWarp_terminal time_order]
  simpa only [hlevel,hhigh,hslack] using hh
end OptimalG.Certificates.ReferenceFlowBoundaryData.CoarseLowerShape
