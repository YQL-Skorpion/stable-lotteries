import OptimalG.Certificates.ReferenceDerivativeWitnessData.CoarseLowerShape
import OptimalG.VariationalUpperTransportLocalization
namespace OptimalG.Certificates.ReferenceCompetitorData.CoarseLowerShape
open Set MeasureTheory Transport Variational ParameterTransfer
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem parameter_range {lam delta : ℝ} (hparam : (TransportReferenceData.CoarseLowerShape.data.lam:ℝ)=lam+delta) : Compact.LambdaRange (lam+delta) := by
  rw [←hparam]
  norm_num [Compact.LambdaRange,TransportReferenceData.CoarseLowerShape.data,TransportReferenceData.CoarseLowerShape.lam]
theorem scalar_range {lam delta : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hdelta : 0≤delta) (hparam : (TransportReferenceData.CoarseLowerShape.data.lam:ℝ)=lam+delta) : Compact.ScalarRange (scalar d.S delta) :=
  shifted_scalar_bounds hd (parameter_range hparam) hdelta
theorem shifted_obstacles {lam delta : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hdelta : 0≤delta) (hparam : (TransportReferenceData.CoarseLowerShape.data.lam:ℝ)=lam+delta) :
    ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,quadratic TransportReferenceData.CoarseLowerShape.data.lam r-scalar d.S delta≤shiftedPrimitive lam d delta r ∧
      shiftedPrimitive lam d delta r≤cap TransportReferenceData.CoarseLowerShape.data.lam (scalar d.S delta) r := by
  intro r hr
  have hl : pLo≤r := by
    have hh : pLo≤ReferenceDisplacementData.CoarseLowerShape.left := by norm_num [pLo,ReferenceDisplacementData.CoarseLowerShape.left,TransportReferenceData.CoarseLowerShape.data,TransportReferenceData.CoarseLowerShape.leftContact]
    exact hh.trans hr.1
  have hu : r≤tEnd := by
    have hh : ReferenceDisplacementData.CoarseLowerShape.right≤tEnd := by norm_num [tEnd,ReferenceDisplacementData.CoarseLowerShape.right,TransportReferenceData.CoarseLowerShape.data,TransportReferenceData.CoarseLowerShape.rightContact]
    exact hr.2.trans hh
  rw [hparam]
  exact ⟨shifted_root_bound hd hdelta ⟨hl,hu.trans (by norm_num [tEnd,zStart])⟩,
    shifted_cap_bound hd hdelta ⟨hl,hu⟩⟩
noncomputable def initial {lam delta : ℝ} {d : LowRankData} {Y : ℝ→ℝ}
    (T : UpwardTransfer lam delta d Y) : ℝ :=
  ReferenceAdjointData.CoarseLowerShape.rho ReferenceActualData.CoarseLowerShape.start*Real.log (1+(quadratic TransportReferenceData.CoarseLowerShape.data.lam ReferenceActualData.CoarseLowerShape.start-scalar d.S delta-
    T.trajectory ReferenceActualData.CoarseLowerShape.start)/ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.start)
theorem initial_nonnegative {lam delta : ℝ} {d : LowRankData} {Y : ℝ→ℝ}
    (hparam : (TransportReferenceData.CoarseLowerShape.data.lam:ℝ)=lam+delta) (T : UpwardTransfer lam delta d Y) : 0 ≤ initial T := by
  have hE : 0≤quadratic TransportReferenceData.CoarseLowerShape.data.lam ReferenceActualData.CoarseLowerShape.start-scalar d.S delta-T.trajectory ReferenceActualData.CoarseLowerShape.start := by
    rw [hparam]
    exact sub_nonneg.mpr (T.upper _ (by norm_num [ReferenceActualData.CoarseLowerShape.start,zStart,zEnd]))
  exact initial_log_deficit_nonneg (Variational.referenceIntegratingFactor_pos _ _ _ _).le
    ReferenceAdjointData.CoarseLowerShape.initial_positive hE
theorem excludes_of_log_flow {lam delta w : ℝ} {d : LowRankData} {Y : ℝ→ℝ}
    (hd : Admissible lam d) (hparam : (TransportReferenceData.CoarseLowerShape.data.lam:ℝ)=lam+delta)
    (hdelta : 0≤delta) (T : UpwardTransfer lam delta d Y)
    (G : StieltjesFunction ℝ) (hleft : Function.leftLim G ReferenceDisplacementData.CoarseLowerShape.left=ReferenceDisplacementData.CoarseLowerShape.left)
    (hmatch : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right ∧
      shiftedPrimitive lam d delta (G r)=TransportReferenceData.CoarseLowerShape.data.transportPrimitive (scalar d.S delta) r)
    (hsq : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,(G r-r)^2≤2*(ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)*matchingVariation G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right)
    (hderiv : ∀ᵐ r ∂volume.restrict (Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right),(3/5:ℝ)≤deriv G r)
    (hflow : initial T+ReferenceCoercivityData.CoarseLowerShape.flow (scalar d.S delta) G-ReferenceCoercivityData.CoarseLowerShape.derivativeFlux G+ReferenceCoercivityData.CoarseLowerShape.entropyFlux G≤w-Real.log (ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish))
    (hfeasible : w≤Real.log (ReferenceEndpointData.CoarseLowerShape.parameters.terminalDeficit (scalar d.S delta))) : False := by
  have hc := ReferenceCoercivityData.CoarseLowerShape.retained_coercivity (scalar_range hd hdelta hparam) G hleft
    (shifted_obstacles hd hdelta hparam) hmatch hsq hderiv hflow hfeasible
  exact ReferenceCoercivityData.CoarseLowerShape.lower_reference_excludes G (initial_nonnegative hparam T)
    (hmatch ReferenceDisplacementData.CoarseLowerShape.right ⟨ReferenceDisplacementData.CoarseLowerShape.rank_order,le_rfl⟩).1.2 hc
end OptimalG.Certificates.ReferenceCompetitorData.CoarseLowerShape
