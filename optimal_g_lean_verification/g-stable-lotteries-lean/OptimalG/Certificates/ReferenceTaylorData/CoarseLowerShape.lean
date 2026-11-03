import OptimalG.Certificates.ReferenceMatchedCoefficients
import OptimalG.Certificates.ReferenceDisplacementData.CoarseLowerShape
import OptimalG.VariationalTransportRemainder
import OptimalG.Certificates.ReferenceSourceRegularity
namespace OptimalG.Certificates.ReferenceTaylorData.CoarseLowerShape
open Set MeasureTheory Transport
open scoped BigOperators
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable def coefficient (S : ℝ) (G : StieltjesFunction ℝ) (i : Fin 4) : ℝ→ℝ :=
  referenceMatchedCoefficient ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cells S G i
noncomputable def source (S : ℝ) (G : StieltjesFunction ℝ) : ℝ→ℝ :=
  Variational.transportCoefficientSource ReferenceAdjointData.CoarseLowerShape.rho (fun z=>Real.log (ReferenceAdjointData.CoarseLowerShape.Z z))
    (fun z i=>coefficient S G i z) (fun z i=>ReferenceAdjointData.CoarseLowerShape.coefficient i z) Variational.transportDelta
noncomputable def linear (S : ℝ) (G : StieltjesFunction ℝ) (z : ℝ) : ℝ :=
  (S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))*ReferencePositionData.CoarseLowerShape.force 0 z+
    ReferenceDisplacementData.CoarseLowerShape.displacement true G z*ReferencePositionData.CoarseLowerShape.force 1 z+ReferenceDisplacementData.CoarseLowerShape.displacement false G z*ReferencePositionData.CoarseLowerShape.force 2 z
theorem coefficient_measurable (S : ℝ) (G : StieltjesFunction ℝ) (i : Fin 4) : Measurable (coefficient S G i) :=
  referenceMatchedCoefficient_measurable ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cells S G.mono.measurable i
theorem matched_order {p : ReferenceScalarCell×HessianCell} (hp : p∈ReferenceTimeData.CoarseLowerShape.Assembly.sources)
    (G : StieltjesFunction ℝ) (hG : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    if p.1.flow.late then p.1.globalMatchedRank false G t≤p.1.globalMatchedRank true G t
      else p.1.globalMatchedRank true G t≤p.1.globalMatchedRank false G t := by
  have hb := List.all_eq_true.mp ReferenceTimeData.CoarseLowerShape.Assembly.branches_checked p hp
  have hpiece : p.1.flow.aPiece.isSome=true := (of_decide_eq_true hb).1
  apply ReferenceScalarCell.branchGeometryCheck_order hb G.mono ht
  have hcentral := ReferenceDisplacementData.CoarseLowerShape.central_rank_range false p.1.flow (by
    rw [←ReferenceTimeData.CoarseLowerShape.Assembly.source_cells]; exact List.mem_map.mpr ⟨p,hp,rfl⟩) t ht
  rw [ReferenceTimeData.CoarseLowerShape.Assembly.source_scalar p hp] at hcentral
  exact (hG _ (hcentral hpiece)).1
theorem cell_taylor {p : ReferenceScalarCell×HessianCell} (hp : p∈ReferenceTimeData.CoarseLowerShape.Assembly.sources)
    {S z : ℝ} (hS : Compact.ScalarRange S) (G : StieltjesFunction ℝ) {Jlow : ℝ→ℝ}
    (hz : z∈Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z)
    (hobstacle : ∀ r∈Icc (p.1.leftContact:ℝ) p.1.rightContact,
      quadratic p.1.flow.lam r-S≤Jlow r ∧ Jlow r≤cap p.1.flow.lam S r)
    (hmatch : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right ∧ Jlow (G r)=TransportReferenceData.CoarseLowerShape.data.transportPrimitive S r) :
    linear S G z+(TransportHessianData.CoarseLowerShapeFlow.scalarField z*(S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))^2-
      TransportHessianData.CoarseLowerShapeFlow.rankField z*((ReferenceDisplacementData.CoarseLowerShape.displacement true G z)^2+(ReferenceDisplacementData.CoarseLowerShape.displacement false G z)^2))/2≤source S G z := by
  have hg := ReferenceTimeData.CoarseLowerShape.Assembly.source_geometry p hp
  have hflow : p.1.flow∈ReferenceActualData.CoarseLowerShape.cells := by
    rw [←ReferenceTimeData.CoarseLowerShape.Assembly.source_cells]; exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have ht := p.1.flow.timeParameter_mem (referenceFlowCoverCheck_bounds ReferenceActualData.CoarseLowerShape.cover_checked hflow).2.1 ⟨hz.1.le,hz.2⟩
  have hmatched (useR : Bool) : p.1.primitiveMatch useR S Jlow (p.1.flow.timeParameter z)
      (p.1.globalMatchedRank useR G (p.1.flow.timeParameter z)) := by
    obtain ⟨bounds,hframe,horder⟩ := ReferenceTimeData.CoarseLowerShape.Assembly.source_rank_frames p hp useR
    exact ReferenceScalarCell.primitiveMatch_of_global_matching TransportReferenceData.CoarseLowerShape.data ReferenceLowData.CoarseLowerShape.checked
      TransportReferenceData.CoarseLowerShape.gauge_checked p.1 useR bounds hframe horder hmatch ht
  have hc := ReferenceHessianWitnessData.CoarseLowerShape.actual_cell_taylor hp hS hz hobstacle (hmatched true) (hmatched false)
    (matched_order hp G (fun r hr=>(hmatch r hr).1) ht)
  dsimp only at hc
  rw [ReferenceFirstWitnessData.CoarseLowerShape.actual_first hp hz] at hc
  have hsource := referenceMatched_source_on_cell ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cover_checked hflow (ReferenceTimeData.CoarseLowerShape.Assembly.source_scalar p hp)
    S G ReferenceAdjointData.CoarseLowerShape.rho ReferenceAdjointData.CoarseLowerShape.Z hz (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) (fun _=>rfl)
  have hs0 : p.1.flow.slack=TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack := congrArg FrozenParameters.referenceSlack hg.1
  have heR : ReferenceDisplacementData.CoarseLowerShape.displacement true G z=p.1.globalMatchedRank true G (p.1.flow.timeParameter z)-ReferenceHessianWitnessData.CoarseLowerShape.frame p z 1 := by
    rw [ReferenceDisplacementData.CoarseLowerShape.displacement_on_cell true G hp hz]
    rfl
  have heA : ReferenceDisplacementData.CoarseLowerShape.displacement false G z=p.1.globalMatchedRank false G (p.1.flow.timeParameter z)-ReferenceHessianWitnessData.CoarseLowerShape.frame p z 2 := by
    rw [ReferenceDisplacementData.CoarseLowerShape.displacement_on_cell false G hp hz]
    rfl
  have hs : source S G z=∑ i∈FrozenParameters.activeTerms p.2.late,ReferenceAdjointData.CoarseLowerShape.weight i z*Real.log
      ((TransportHessianData.CoarseLowerShapeFlow.params.coefficients p.2.late i).eval
        (FrozenParameters.comparisonChord (ReferenceHessianWitnessData.CoarseLowerShape.frame p z) (S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))
          (ReferenceDisplacementData.CoarseLowerShape.displacement true G z) (ReferenceDisplacementData.CoarseLowerShape.displacement false G z) 1)/
       (TransportHessianData.CoarseLowerShapeFlow.params.coefficients p.2.late i).eval (ReferenceHessianWitnessData.CoarseLowerShape.frame p z)) := by
    simpa only [source,coefficient,ReferenceAdjointData.CoarseLowerShape.coefficient,ReferenceScalarCell.endpointChord,hg.1,hg.2.1,hs0,
      ReferenceHessianWitnessData.CoarseLowerShape.frame,heR,heA] using hsource
  rw [hs,linear,heR,heA]
  exact hc
theorem global_taylor {S : ℝ} (hS : Compact.ScalarRange S) (G : StieltjesFunction ℝ) {Jlow : ℝ→ℝ}
    (hobstacle : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,quadratic TransportReferenceData.CoarseLowerShape.data.lam r-S≤Jlow r ∧ Jlow r≤cap TransportReferenceData.CoarseLowerShape.data.lam S r)
    (hmatch : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right ∧ Jlow (G r)=TransportReferenceData.CoarseLowerShape.data.transportPrimitive S r)
    {z : ℝ} (hz : z∈Ioc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish) :
    linear S G z+(TransportHessianData.CoarseLowerShapeFlow.scalarField z*(S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))^2-
      TransportHessianData.CoarseLowerShapeFlow.rankField z*((ReferenceDisplacementData.CoarseLowerShape.displacement true G z)^2+(ReferenceDisplacementData.CoarseLowerShape.displacement false G z)^2))/2≤source S G z := by
  obtain ⟨p,hp,hzp,_⟩ := ReferenceTimeData.CoarseLowerShape.Assembly.selected_actual_frame hz
  apply cell_taylor hp hS G hzp _ hmatch
  have hs := ReferenceTimeData.CoarseLowerShape.Assembly.source_scalar p hp
  have hl : p.1.leftContact=TransportReferenceData.CoarseLowerShape.data.leftContact := by rw [←hs]; rfl
  have hr : p.1.rightContact=TransportReferenceData.CoarseLowerShape.data.rightContact := by rw [←hs]; rfl
  have hL : p.1.flow.lam=TransportReferenceData.CoarseLowerShape.data.lam := congrArg FrozenParameters.lam (ReferenceTimeData.CoarseLowerShape.Assembly.source_geometry p hp).1
  simpa only [hl,hr,hL,ReferenceDisplacementData.CoarseLowerShape.left,ReferenceDisplacementData.CoarseLowerShape.right] using hobstacle
theorem source_cell_bounded {p : ReferenceScalarCell×HessianCell} (hp : p∈ReferenceTimeData.CoarseLowerShape.Assembly.sources)
    {S : ℝ} (hS : Compact.ScalarRange S) (G : StieltjesFunction ℝ) {Jlow : ℝ→ℝ}
    (hobstacle : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,quadratic TransportReferenceData.CoarseLowerShape.data.lam r-S≤Jlow r ∧ Jlow r≤cap TransportReferenceData.CoarseLowerShape.data.lam S r)
    (hmatch : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right ∧ Jlow (G r)=TransportReferenceData.CoarseLowerShape.data.transportPrimitive S r) :
    ∃ B : ℝ,0≤B ∧ ∀ z∈Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,|source S G z|≤B := by
  obtain ⟨B,hB,hbound⟩ := HessianCell.checkedClean_weighted_log_ratio_bounded TransportHessianData.CoarseLowerShapeFlow.scale_pos
    TransportHessianData.CoarseLowerShapeFlow.endpoints_ordered TransportHessianData.CoarseLowerShapeFlow.slabs_checked (ReferenceTimeData.CoarseLowerShape.Assembly.source_checked hp)
  refine ⟨2*B,by positivity,?_⟩
  intro z hz
  have hg := ReferenceTimeData.CoarseLowerShape.Assembly.source_geometry p hp
  have hflow : p.1.flow∈ReferenceActualData.CoarseLowerShape.cells := by
    rw [←ReferenceTimeData.CoarseLowerShape.Assembly.source_cells]; exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have ht := p.1.flow.timeParameter_mem (referenceFlowCoverCheck_bounds ReferenceActualData.CoarseLowerShape.cover_checked hflow).2.1 ⟨hz.1.le,hz.2⟩
  have hmatched (useR : Bool) : p.1.primitiveMatch useR S Jlow (p.1.flow.timeParameter z)
      (p.1.globalMatchedRank useR G (p.1.flow.timeParameter z)) := by
    obtain ⟨bounds,hframe,horder⟩ := ReferenceTimeData.CoarseLowerShape.Assembly.source_rank_frames p hp useR
    exact ReferenceScalarCell.primitiveMatch_of_global_matching TransportReferenceData.CoarseLowerShape.data ReferenceLowData.CoarseLowerShape.checked
      TransportReferenceData.CoarseLowerShape.gauge_checked p.1 useR bounds hframe horder hmatch ht
  have hcell := ReferenceTimeData.CoarseLowerShape.Assembly.source_scalar p hp
  have hleft : p.1.leftContact=TransportReferenceData.CoarseLowerShape.data.leftContact := by rw [←hcell]; rfl
  have hright : p.1.rightContact=TransportReferenceData.CoarseLowerShape.data.rightContact := by rw [←hcell]; rfl
  have hLam : p.1.flow.lam=TransportReferenceData.CoarseLowerShape.data.lam := congrArg FrozenParameters.lam hg.1
  have hlocal : ∀ r∈Icc (p.1.leftContact:ℝ) p.1.rightContact,
      quadratic p.1.flow.lam r-S≤Jlow r ∧ Jlow r≤cap p.1.flow.lam S r := by
    simpa only [hleft,hright,hLam,ReferenceDisplacementData.CoarseLowerShape.left,ReferenceDisplacementData.CoarseLowerShape.right] using hobstacle
  have hSl : S≤(3:ℝ)/100 := by have hh:=hS.2; norm_num [Compact.scalarUpper] at hh; linarith
  have hL : Compact.LambdaRange p.1.flow.lam := by rw [hLam]; norm_num [Compact.LambdaRange,TransportReferenceData.CoarseLowerShape.data,TransportReferenceData.CoarseLowerShape.lam]
  have hend := ReferenceTimeData.CoarseLowerShape.Assembly.matched_endpoints p hp S Jlow hL hSl hlocal (ReferenceHessianWitnessData.CoarseLowerShape.compact_scalar_contains hS)
    _ ht _ _ (hmatched true) (hmatched false) (matched_order hp G (fun r hr=>(hmatch r hr).1) ht)
  let x := ReferenceHessianWitnessData.CoarseLowerShape.frame p z
  let y := p.1.endpointChord (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) S
    (p.1.globalMatchedRank true G (p.1.flow.timeParameter z))
    (p.1.globalMatchedRank false G (p.1.flow.timeParameter z))
  have hbase : ∀ j,(p.2.fixed j).Contains TransportHessianData.CoarseLowerShapeFlow.scale (x j.succ) := ReferenceTimeData.CoarseLowerShape.Assembly.actual_frames p hp z hz
  have hs0 : p.1.flow.slack=TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack := congrArg FrozenParameters.referenceSlack hg.1
  have hx0 : x 0=(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ) := by
    change (p.1.flow.slack:ℝ)=_; exact_mod_cast hs0
  have hxS : (⟨TransportHessianData.CoarseLowerShapeFlow.start,TransportHessianData.CoarseLowerShapeFlow.finish⟩:IntegerInterval).Contains TransportHessianData.CoarseLowerShapeFlow.scale (x 0) := by
    rw [hx0,←ReferenceHessianWitnessData.CoarseLowerShape.scalar_box_link]; exact ReferenceHessianWitnessData.CoarseLowerShape.reference_scalar_contains
  have hyS : (⟨TransportHessianData.CoarseLowerShapeFlow.start,TransportHessianData.CoarseLowerShapeFlow.finish⟩:IntegerInterval).Contains TransportHessianData.CoarseLowerShapeFlow.scale (y 0) := by
    rw [show y 0=S from (p.1.endpointChord_coordinates _ _ _ _ _).1,←ReferenceHessianWitnessData.CoarseLowerShape.scalar_box_link]
    exact ReferenceHessianWitnessData.CoarseLowerShape.compact_scalar_contains hS
  have hyf : ∀ j,(p.2.fixed j).Contains TransportHessianData.CoarseLowerShapeFlow.scale (y j.succ) := by
    intro j
    by_cases h0 : j=0
    · subst j
      change (p.2.fixed 0).Contains TransportHessianData.CoarseLowerShapeFlow.scale (y 1)
      rw [show y 1=p.1.globalMatchedRank true G (p.1.flow.timeParameter z) from (p.1.endpointChord_coordinates _ _ _ _ _).2.1]
      simpa only [ReferenceSensitivityData.CoarseLowerShape.scale,TransportHessianData.CoarseLowerShapeFlow.scale] using hend.1
    by_cases h1 : j=1
    · subst j
      change (p.2.fixed 1).Contains TransportHessianData.CoarseLowerShapeFlow.scale (y 2)
      rw [show y 2=p.1.globalMatchedRank false G (p.1.flow.timeParameter z) from (p.1.endpointChord_coordinates _ _ _ _ _).2.2.1]
      simpa only [ReferenceSensitivityData.CoarseLowerShape.scale,TransportHessianData.CoarseLowerShapeFlow.scale] using hend.2
    have hd : FrozenParameters.threeDirection (S-p.1.flow.slack)
        (p.1.globalMatchedRank true G (p.1.flow.timeParameter z)-x 1)
        (p.1.globalMatchedRank false G (p.1.flow.timeParameter z)-x 2) j.succ=0 := by
      fin_cases j <;> simp_all [FrozenParameters.threeDirection]
    change (p.2.fixed j).Contains TransportHessianData.CoarseLowerShapeFlow.scale
      (x j.succ + 1*FrozenParameters.threeDirection (S-p.1.flow.slack)
        (p.1.globalMatchedRank true G (p.1.flow.timeParameter z)-x 1)
        (p.1.globalMatchedRank false G (p.1.flow.timeParameter z)-x 2) j.succ)
    simpa only [hd,mul_zero,add_zero] using hbase j
  have hw : ∀ i : Fin 4,y ⟨12+i.val,by omega⟩=x ⟨12+i.val,by omega⟩ :=
    fun i=>FrozenParameters.comparisonChord_weight _ _ _ _ _ i
  have hh := hbound x y hxS hbase hyS hyf hw
  have hsource := referenceMatched_source_on_cell ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cover_checked hflow hcell S G
    ReferenceAdjointData.CoarseLowerShape.rho ReferenceAdjointData.CoarseLowerShape.Z hz (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) (fun _=>rfl)
  have hweights (i : Fin 4) : x ⟨12+i.val,by omega⟩=ReferenceAdjointData.CoarseLowerShape.weight i z := by
    fin_cases i <;> rfl
  have hs : source S G z=∑ i∈FrozenParameters.activeTerms p.2.late,ReferenceAdjointData.CoarseLowerShape.weight i z*Real.log
      ((TransportHessianData.CoarseLowerShapeFlow.params.coefficients p.2.late i).eval y/(TransportHessianData.CoarseLowerShapeFlow.params.coefficients p.2.late i).eval x) := by
    simpa only [source,coefficient,ReferenceAdjointData.CoarseLowerShape.coefficient,hg.1,hg.2.1,x,y,ReferenceHessianWitnessData.CoarseLowerShape.frame] using hsource
  rw [hs]
  simpa only [hweights] using hh
theorem source_bounded {S : ℝ} (hS : Compact.ScalarRange S) (G : StieltjesFunction ℝ) {Jlow : ℝ→ℝ}
    (hobstacle : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,quadratic TransportReferenceData.CoarseLowerShape.data.lam r-S≤Jlow r ∧ Jlow r≤cap TransportReferenceData.CoarseLowerShape.data.lam S r)
    (hmatch : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right ∧ Jlow (G r)=TransportReferenceData.CoarseLowerShape.data.transportPrimitive S r) :
    ∃ B : ℝ,0≤B ∧ ∀ z∈Ioc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish,|source S G z|≤B := by
  obtain ⟨B,hB,hbounds⟩ := finite_cell_uniform_bound ReferenceTimeData.CoarseLowerShape.Assembly.sources
    (fun p=>Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z) (source S G)
    (fun p hp=>source_cell_bounded hp hS G hobstacle hmatch)
  refine ⟨B,hB,?_⟩
  intro z hz
  obtain ⟨p,hp,hzp,_⟩ := ReferenceTimeData.CoarseLowerShape.Assembly.selected_actual_frame hz
  exact hbounds p hp z hzp
theorem source_integrable {S : ℝ} (hS : Compact.ScalarRange S) (G : StieltjesFunction ℝ) {Jlow : ℝ→ℝ}
    (hobstacle : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,quadratic TransportReferenceData.CoarseLowerShape.data.lam r-S≤Jlow r ∧ Jlow r≤cap TransportReferenceData.CoarseLowerShape.data.lam S r)
    (hmatch : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right ∧ Jlow (G r)=TransportReferenceData.CoarseLowerShape.data.transportPrimitive S r) :
    IntervalIntegrable (source S G) volume (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish := by
  obtain ⟨B,_,hB⟩ := source_bounded hS G hobstacle hmatch
  exact transportCoefficientSource_intervalIntegrable ReferenceFirstWitnessData.CoarseLowerShape.time_order
    (by simpa only [uIcc_of_le ReferenceFirstWitnessData.CoarseLowerShape.time_order] using ReferenceAdjointData.CoarseLowerShape.Z_spec.2.1.continuousOn)
    (by simpa only [uIcc_of_le ReferenceFirstWitnessData.CoarseLowerShape.time_order] using ReferenceFirstWitnessData.CoarseLowerShape.exponential_continuous)
    (fun z hz=>ReferenceFirstWitnessData.CoarseLowerShape.actual_adjoint hz) Variational.transportDelta
    (coefficient_measurable S G) (referenceCoefficient_measurable ReferenceActualData.CoarseLowerShape.cells) hB
theorem linear_integrable (S : ℝ) (G : StieltjesFunction ℝ)
    (hG : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right)
    (hsq : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,(G r-r)^2≤2*(ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)*Variational.matchingVariation G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right) :
    IntervalIntegrable (linear S G) volume (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish :=
  ((ReferenceFirstWitnessData.CoarseLowerShape.force_scalar_integrable.const_mul _).add
    (ReferenceDisplacementData.CoarseLowerShape.displacement_force_integrable true 1 (Or.inl rfl) G hG hsq)).add
      (ReferenceDisplacementData.CoarseLowerShape.displacement_force_integrable false 2 (Or.inr rfl) G hG hsq)
theorem linear_integral (S : ℝ) (G : StieltjesFunction ℝ)
    (hG : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right)
    (hsq : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,(G r-r)^2≤2*(ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)*Variational.matchingVariation G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right) :
    (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,linear S G z)=
      (S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))*(ReferenceBudgetData.CoarseLowerShape.V ReferenceActualData.CoarseLowerShape.finish/ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish)+
        (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,ReferenceDisplacementData.CoarseLowerShape.displacement true G z*ReferencePositionData.CoarseLowerShape.force 1 z)+
        (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,ReferenceDisplacementData.CoarseLowerShape.displacement false G z*ReferencePositionData.CoarseLowerShape.force 2 z) := by
  have h0 := ReferenceFirstWitnessData.CoarseLowerShape.force_scalar_integrable.const_mul (S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))
  have h1 := ReferenceDisplacementData.CoarseLowerShape.displacement_force_integrable true 1 (Or.inl rfl) G hG hsq
  have h2 := ReferenceDisplacementData.CoarseLowerShape.displacement_force_integrable false 2 (Or.inr rfl) G hG hsq
  unfold linear
  rw [intervalIntegral.integral_add (h0.add h1) h2,
    intervalIntegral.integral_add h0 h1,intervalIntegral.integral_const_mul,ReferenceFirstWitnessData.CoarseLowerShape.force_scalar_integral]
theorem integrated_taylor_of_integrable {S : ℝ} (hS : Compact.ScalarRange S)
    (G : StieltjesFunction ℝ) {Jlow : ℝ→ℝ}
    (hobstacle : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,quadratic TransportReferenceData.CoarseLowerShape.data.lam r-S≤Jlow r ∧ Jlow r≤cap TransportReferenceData.CoarseLowerShape.data.lam S r)
    (hmatch : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right ∧ Jlow (G r)=TransportReferenceData.CoarseLowerShape.data.transportPrimitive S r)
    (hsq : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,(G r-r)^2≤2*(ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)*Variational.matchingVariation G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right)
    (hsource : IntervalIntegrable (source S G) volume (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish) :
    (S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))*(ReferenceBudgetData.CoarseLowerShape.V ReferenceActualData.CoarseLowerShape.finish/ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish)+
      (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,ReferenceDisplacementData.CoarseLowerShape.displacement true G z*ReferencePositionData.CoarseLowerShape.force 1 z)+
      (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,ReferenceDisplacementData.CoarseLowerShape.displacement false G z*ReferencePositionData.CoarseLowerShape.force 2 z)+
      ((TransportHessianData.CoarseLowerShapeFlow.scalarMass:ℝ)/2)*(S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))^2-
      (2*(ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)*(TransportHessianData.CoarseLowerShapeFlow.rankMass:ℝ))*Variational.matchingVariation G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right≤
        ∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,source S G z := by
  have hG := fun r hr=>(hmatch r hr).1
  have hi := linear_integrable S G hG hsq
  have hms : IntervalIntegrable TransportHessianData.CoarseLowerShapeFlow.scalarField volume (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish := TransportHessianData.CoarseLowerShapeFlow.scalar_integrable
  have hmr : IntervalIntegrable TransportHessianData.CoarseLowerShapeFlow.rankField volume (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish := TransportHessianData.CoarseLowerShapeFlow.rank_integrable
  have hbound := Variational.transport_integrated_taylor
    (mu:=volume.restrict (Ioc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish))
    (ds:=S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ)) (length:=ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)
    (V:=Variational.matchingVariation G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right)
    (e1:=ReferenceDisplacementData.CoarseLowerShape.displacement true G) (e2:=ReferenceDisplacementData.CoarseLowerShape.displacement false G)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ReferenceFirstWitnessData.CoarseLowerShape.time_order).mp hsource)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ReferenceFirstWitnessData.CoarseLowerShape.time_order).mp hi)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ReferenceFirstWitnessData.CoarseLowerShape.time_order).mp hms)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ReferenceFirstWitnessData.CoarseLowerShape.time_order).mp hmr)
    (Filter.Eventually.of_forall TransportHessianData.CoarseLowerShapeFlow.rank_nonnegative)
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with z hz
      exact (ReferenceDisplacementData.CoarseLowerShape.displacement_bounds true G hG hsq hz).2)
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with z hz
      exact (ReferenceDisplacementData.CoarseLowerShape.displacement_bounds false G hG hsq hz).2)
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with z hz
      have hh := global_taylor hS G hobstacle hmatch hz
      nlinarith only [hh])
  rw [←intervalIntegral.integral_of_le ReferenceFirstWitnessData.CoarseLowerShape.time_order,
    ←intervalIntegral.integral_of_le ReferenceFirstWitnessData.CoarseLowerShape.time_order,
    ←intervalIntegral.integral_of_le ReferenceFirstWitnessData.CoarseLowerShape.time_order,
    ←intervalIntegral.integral_of_le ReferenceFirstWitnessData.CoarseLowerShape.time_order] at hbound
  have hsi : (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,TransportHessianData.CoarseLowerShapeFlow.scalarField z)=(TransportHessianData.CoarseLowerShapeFlow.scalarMass:ℝ) := TransportHessianData.CoarseLowerShapeFlow.scalar_integral
  have hri : (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,TransportHessianData.CoarseLowerShapeFlow.rankField z)=(TransportHessianData.CoarseLowerShapeFlow.rankMass:ℝ) := TransportHessianData.CoarseLowerShapeFlow.rank_integral
  rw [linear_integral S G hG hsq,hsi,hri] at hbound
  convert hbound using 1 <;> ring
theorem integrated_taylor {S : ℝ} (hS : Compact.ScalarRange S)
    (G : StieltjesFunction ℝ) {Jlow : ℝ→ℝ}
    (hobstacle : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,quadratic TransportReferenceData.CoarseLowerShape.data.lam r-S≤Jlow r ∧ Jlow r≤cap TransportReferenceData.CoarseLowerShape.data.lam S r)
    (hmatch : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right ∧ Jlow (G r)=TransportReferenceData.CoarseLowerShape.data.transportPrimitive S r)
    (hsq : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,(G r-r)^2≤2*(ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)*Variational.matchingVariation G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right) :
    (S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))*(ReferenceBudgetData.CoarseLowerShape.V ReferenceActualData.CoarseLowerShape.finish/ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish)+
      (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,ReferenceDisplacementData.CoarseLowerShape.displacement true G z*ReferencePositionData.CoarseLowerShape.force 1 z)+
      (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,ReferenceDisplacementData.CoarseLowerShape.displacement false G z*ReferencePositionData.CoarseLowerShape.force 2 z)+
      ((TransportHessianData.CoarseLowerShapeFlow.scalarMass:ℝ)/2)*(S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))^2-
      (2*(ReferenceDisplacementData.CoarseLowerShape.right-ReferenceDisplacementData.CoarseLowerShape.left)*(TransportHessianData.CoarseLowerShapeFlow.rankMass:ℝ))*Variational.matchingVariation G ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right≤
        ∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,source S G z :=
  integrated_taylor_of_integrable hS G hobstacle hmatch hsq (source_integrable hS G hobstacle hmatch)
end OptimalG.Certificates.ReferenceTaylorData.CoarseLowerShape
