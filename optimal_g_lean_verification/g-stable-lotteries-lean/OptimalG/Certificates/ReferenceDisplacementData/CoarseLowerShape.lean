import OptimalG.Certificates.ReferenceMatchedDisplacement
import OptimalG.Certificates.ReferenceFirstWitnessData.CoarseLowerShape
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Assembly
namespace OptimalG.Certificates.ReferenceDisplacementData.CoarseLowerShape
open Set MeasureTheory Transport
noncomputable abbrev left : ℝ := TransportReferenceData.CoarseLowerShape.data.leftContact
noncomputable abbrev right : ℝ := TransportReferenceData.CoarseLowerShape.data.rightContact
noncomputable def displacement (useR : Bool) (G : StieltjesFunction ℝ) : ℝ→ℝ :=
  referenceDisplacement ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cells useR G
theorem rank_order : left≤right := by norm_num [left,right,TransportReferenceData.CoarseLowerShape.data,TransportReferenceData.CoarseLowerShape.leftContact,TransportReferenceData.CoarseLowerShape.rightContact]
theorem tail_frame_checked : TransportReferenceData.CoarseLowerShape.data.tailFrameCheck=true := by decide +kernel
theorem central_rank_range (useR : Bool) : ∀ c∈ReferenceActualData.CoarseLowerShape.cells,∀ t∈Icc (0:ℝ) 1,
    ((ReferenceSensitivityData.CoarseLowerShape.makeCell c).rankProfile useR ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).piece.isSome=true →
      (ReferenceSensitivityData.CoarseLowerShape.makeCell c).referenceRank useR t∈Icc left right := by
  intro c hc t ht hp
  rw [←ReferenceTimeData.CoarseLowerShape.Assembly.source_cells] at hc
  obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hc
  rw [ReferenceTimeData.CoarseLowerShape.Assembly.source_scalar p hp'] at hp ⊢
  obtain ⟨bounds,hframe,horder⟩ := ReferenceTimeData.CoarseLowerShape.Assembly.source_rank_frames p hp' useR
  have hpiece : (p.1.rankProfile useR bounds).piece.isSome=true := by cases useR <;> exact hp
  exact ReferenceProfileCell.frameCheck_central_mem TransportReferenceData.CoarseLowerShape.data _ hframe hpiece
    (p.1.referenceRank_mem useR bounds horder ht)
theorem displacement_measurable (useR : Bool) (G : StieltjesFunction ℝ) : Measurable (displacement useR G) :=
  referenceDisplacement_measurable ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cells useR G.mono.measurable
theorem displacement_bounds (useR : Bool) (G : StieltjesFunction ℝ)
    (hG : ∀ r∈Icc left right,G r∈Icc left right)
    (hsq : ∀ r∈Icc left right,(G r-r)^2≤2*(right-left)*Variational.matchingVariation G left right)
    {z : ℝ} (hz : z∈Ioc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish) :
    |displacement useR G z|≤right-left ∧ (displacement useR G z)^2≤
      2*(right-left)*Variational.matchingVariation G left right :=
  referenceDisplacement_bounds ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cover_checked useR rank_order G hG hsq
    (central_rank_range useR) hz
theorem displacement_on_cell (useR : Bool) (G : StieltjesFunction ℝ)
    {p : ReferenceScalarCell×HessianCell} (hp : p∈ReferenceTimeData.CoarseLowerShape.Assembly.sources)
    {z : ℝ} (hz : z∈Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z) :
    displacement useR G z=p.1.matchedDisplacement useR G (p.1.flow.timeParameter z) := by
  have hm : p.1.flow∈ReferenceActualData.CoarseLowerShape.cells := by
    rw [←ReferenceTimeData.CoarseLowerShape.Assembly.source_cells]; exact List.mem_map.mpr ⟨p,hp,rfl⟩
  exact referenceDisplacement_on_cell ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cover_checked hm (ReferenceTimeData.CoarseLowerShape.Assembly.source_scalar p hp) useR G hz
theorem displacement_force_integrable (useR : Bool) (j : Fin 16) (hj : j=1 ∨ j=2)
    (G : StieltjesFunction ℝ) (hG : ∀ r∈Icc left right,G r∈Icc left right)
    (hsq : ∀ r∈Icc left right,(G r-r)^2≤2*(right-left)*Variational.matchingVariation G left right) :
    IntervalIntegrable (fun z=>displacement useR G z*ReferencePositionData.CoarseLowerShape.force j z) volume (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ReferenceFirstWitnessData.CoarseLowerShape.time_order).mpr
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le ReferenceFirstWitnessData.CoarseLowerShape.time_order).mp (ReferenceFirstWitnessData.CoarseLowerShape.force_rank_integrable j hj)
  apply hi.bdd_mul (displacement_measurable useR G).aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with z hz
  simpa only [Real.norm_eq_abs] using (displacement_bounds useR G hG hsq hz).1
theorem actual_matching_exists {lam delta : ℝ} {d : Variational.LowRankData}
    (hd : Variational.Admissible lam d) (hdelta : 0≤delta) (hparam : (TransportReferenceData.CoarseLowerShape.data.lam:ℝ)=lam+delta) :
    ∃ G : StieltjesFunction ℝ,Function.leftLim G left=left ∧
      (∀ r∈Icc left right,G r∈Icc left right ∧ Variational.ParameterTransfer.shiftedPrimitive lam d delta (G r)=
        TransportReferenceData.CoarseLowerShape.data.transportPrimitive (Variational.ParameterTransfer.scalar d.S delta) r) ∧
      (∀ᵐ r ∂volume.restrict (Icc left right),HasDerivAt G (deriv G r) r ∧ 0<deriv G r ∧ (3/5:ℝ)≤deriv G r ∧
        d.phi (G r)=TransportReferenceData.CoarseLowerShape.data.transportScore (Variational.ParameterTransfer.scalar d.S delta) r/deriv G r ∧
        (G r,d.phi (G r))∈Variational.rankScoreSupport d.phi) ∧
      ∀ r∈Icc left right,(G r-r)^2≤2*(right-left)*Variational.matchingVariation G left right := by
  have hL : Compact.LambdaRange (lam+delta) := by
    rw [←hparam]; norm_num [Compact.LambdaRange,TransportReferenceData.CoarseLowerShape.data,TransportReferenceData.CoarseLowerShape.lam]
  have hscalar := ReferenceHessianWitnessData.CoarseLowerShape.compact_scalar_contains (Variational.ParameterTransfer.shifted_scalar_bounds hd hL hdelta)
  apply TransportReferenceData.CoarseLowerShape.data.transferred_matching_exists hd hdelta hparam ReferenceLowData.CoarseLowerShape.checked TransportReferenceData.CoarseLowerShape.gauge_checked tail_frame_checked
  · norm_num [Variational.xLo,TransportReferenceData.CoarseLowerShape.data,TransportReferenceData.CoarseLowerShape.leftContact]
  · norm_num [Variational.pHi,TransportReferenceData.CoarseLowerShape.data,TransportReferenceData.CoarseLowerShape.rightContact]
  · intro r hr
    exact ReferenceProfileData.CoarseLowerShape.Assembly.global_shifted_score _ r hscalar hr
end OptimalG.Certificates.ReferenceDisplacementData.CoarseLowerShape
