import OptimalG.Certificates.ReferenceGlobalTolerance
import OptimalG.Certificates.ReferencePositiveData.CoarseLowerShape
import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Assembly
import OptimalG.Certificates.ReferenceInitialAdjointData.CoarseLowerShape
namespace OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
open Set MeasureTheory Transport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable def Z : ℝ→ℝ := Classical.choose ReferencePositiveData.CoarseLowerShape.actual_positive_solution
theorem Z_spec :
    Z ReferenceActualData.CoarseLowerShape.start=ReferenceActualData.CoarseLowerShape.referenceCubic ReferenceActualData.CoarseLowerShape.start ∧
    AbsolutelyContinuousOnInterval Z ReferenceActualData.CoarseLowerShape.start ReferenceActualData.CoarseLowerShape.finish ∧
    (∀ᵐ z ∂volume.restrict (Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish),
      deriv Z z=ReferenceActualData.CoarseLowerShape.alpha z*Z z+ReferenceActualData.CoarseLowerShape.beta z) ∧
    (∀ z∈Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish,|Z z-ReferenceActualData.CoarseLowerShape.referenceCubic z|≤(ReferenceActualData.CoarseLowerShape.flowRate:ℝ)*(z-ReferenceActualData.CoarseLowerShape.start)) ∧
    (∀ z∈Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish,0<Z z) :=
  Classical.choose_spec ReferencePositiveData.CoarseLowerShape.actual_positive_solution
noncomputable def rho (z : ℝ) : ℝ := Variational.referenceIntegratingFactor ReferenceActualData.CoarseLowerShape.start ReferenceActualData.CoarseLowerShape.finish (fun t=>ReferenceActualData.CoarseLowerShape.beta t/Z t) z
noncomputable def coefficient (i : Fin 4) : ℝ→ℝ := referenceCoefficient ReferenceActualData.CoarseLowerShape.cells i
noncomputable def weight (i : Fin 4) (z : ℝ) : ℝ :=
  rho z*Variational.referenceWeight (coefficient i z) (Variational.transportDelta i) (Real.log (Z z))
theorem terminal_contains : ReferenceWeightData.CoarseLowerShape.terminal.Contains ReferenceWeightData.CoarseLowerShape.scale (Z ReferenceActualData.CoarseLowerShape.finish) := by
  have hg := ReferenceEndpointLinkData.CoarseLowerShape.X_last_geometry
  have hfinish : ReferenceCurveData.CoarseLowerShape.piece347.hi=ReferenceActualData.CoarseLowerShape.finish := hg.2
  apply checked_trajectory_endpoint ReferenceCurveData.CoarseLowerShape.assembly_checked ReferenceEndpointLinkData.CoarseLowerShape.X_last_member hg.1 ReferenceWeightData.CoarseLowerShape.terminal_checked
  rw [hfinish]
  convert Z_spec.2.2.2.1 ReferenceActualData.CoarseLowerShape.finish ⟨by norm_num [ReferenceActualData.CoarseLowerShape.start,ReferenceActualData.CoarseLowerShape.finish],le_rfl⟩ using 1 <;> norm_num [ReferenceActualData.CoarseLowerShape.flowRate,ReferenceActualData.CoarseLowerShape.start,ReferenceActualData.CoarseLowerShape.finish]
  all_goals rfl
theorem exponent_contains {c : ReferenceWeightCertificate} (hc : c∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates)
    {z : ℝ} (hz : z∈Icc (c.cell.flow.segment.left.z:ℝ) c.cell.flow.segment.right.z) :
    c.cell.exponent.Contains ReferenceWeightData.CoarseLowerShape.scale (∫ x in z..(ReferenceActualData.CoarseLowerShape.finish:ℝ),ReferenceActualData.CoarseLowerShape.alpha x) := by
  rw [←ReferenceExponentData.CoarseLowerShape.Assembly.weights_linked] at hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  exact ReferenceExponentData.CoarseLowerShape.Assembly.actual_exponents d hd z hz
theorem exponential_contains {c : ReferenceWeightCertificate} (hc : c∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates)
    {z : ℝ} (hz : z∈Icc (c.cell.flow.segment.left.z:ℝ) c.cell.flow.segment.right.z) :
    c.cell.exponential.Contains ReferenceWeightData.CoarseLowerShape.scale (Real.exp (∫ x in z..(ReferenceActualData.CoarseLowerShape.finish:ℝ),ReferenceActualData.CoarseLowerShape.alpha x)) := by
  have hweight := List.all_eq_true.mp ReferenceWeightData.CoarseLowerShape.Assembly.checked c hc
  have hcell := (Bool.and_eq_true_iff.mp hweight).2
  have hexp := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcell).2).1
  exact IntegerInterval.expRefinedCheck_sound (by norm_num [ReferenceWeightData.CoarseLowerShape.scale])
    (by norm_num [ReferenceWeightData.CoarseLowerShape.multiplier]) hexp (exponent_contains hc hz)
theorem weights_contain {c : ReferenceWeightCertificate} (hc : c∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates)
    {z : ℝ} (hz : z∈Ioc (c.cell.flow.segment.left.z:ℝ) c.cell.flow.segment.right.z)
    (i : Fin 4) : (c.cell.weights i).Contains ReferenceWeightData.CoarseLowerShape.scale (weight i z) := by
  obtain ⟨parent,hp,lo,hi,hr⟩ := ReferenceWeightData.CoarseLowerShape.Assembly.refined c hc
  have hpieces : ReferenceActualData.CoarseLowerShape.cells.map ReferenceFlowCell.canonicalPiece=ReferenceCurveData.CoarseLowerShape.pieces := by
    simpa only [ReferenceActualData.CoarseLowerShape.cells,List.map_map,Function.comp_def] using ReferenceActualData.CoarseLowerShape.pieces_checked.symm
  have hpoly : ReferenceActualData.CoarseLowerShape.cells.all ReferenceFlowCell.canonicalPieceCheck=true := by
    simpa only [ReferenceActualData.CoarseLowerShape.cells,List.all_map,Function.comp_def] using ReferenceActualData.CoarseLowerShape.polynomials_checked
  have hpiece : parent.canonicalPiece∈ReferenceCurveData.CoarseLowerShape.pieces := by
    rw [←hpieces]
    exact List.mem_map.mpr ⟨parent,hp,rfl⟩
  have hstart : c.start=ReferenceActualData.CoarseLowerShape.start := of_decide_eq_true (List.all_eq_true.mp ReferenceWeightData.CoarseLowerShape.Assembly.starts_checked c hc)
  have hterm : c.cell.terminal=ReferenceWeightData.CoarseLowerShape.terminal := of_decide_eq_true (List.all_eq_true.mp ReferenceWeightData.CoarseLowerShape.Assembly.terminals_checked c hc)
  apply checked_refined_adjoint_weights_with_error (rate:=(ReferenceActualData.CoarseLowerShape.flowRate:ℝ))
    (s:=ReferenceWeightData.CoarseLowerShape.scale) (k:=ReferenceWeightData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceWeightData.CoarseLowerShape.scale]) (by norm_num [ReferenceWeightData.CoarseLowerShape.multiplier])
    c ((c.cell.flow.segment.right.z-c.start)/500000) (List.all_eq_true.mp ReferenceWeightData.CoarseLowerShape.Assembly.checked c hc) ReferenceActualData.CoarseLowerShape.cover_checked hp hr
    ReferenceCurveData.CoarseLowerShape.assembly_checked hpiece (List.all_eq_true.mp hpoly parent hp)
    (by norm_num [ReferenceActualData.CoarseLowerShape.flowRate]) (by rw [hstart]; simp only [Rat.cast_div,Rat.cast_sub,Rat.cast_ofNat,ReferenceActualData.CoarseLowerShape.flowRate]; exact le_of_eq (by ring))
    Z_spec.2.2.2.1 ReferenceActualData.CoarseLowerShape.alpha_intervalIntegrable ReferenceActualData.CoarseLowerShape.beta_intervalIntegrable
    Z_spec.2.1 Z_spec.2.2.2.2 Z_spec.2.2.1 hz (exponent_contains hc ⟨hz.1.le,hz.2⟩)
  rw [hterm]
  exact terminal_contains
theorem weights_nonnegative_on_cell {c : ReferenceWeightCertificate} (hc : c∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates)
    {z : ℝ} (hz : z∈Ioc (c.cell.flow.segment.left.z:ℝ) c.cell.flow.segment.right.z)
    (i : Fin 4) : 0≤weight i z := by
  have hp := List.all_eq_true.mp ReferenceWeightData.CoarseLowerShape.Assembly.positivity_checked c hc
  have hlo : 0≤(c.cell.weights i).lo := (of_decide_eq_true
    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hp).2 i (List.mem_finRange i)) :
      0≤(c.cell.weights i).lo ∧ ((c.cell.flow.late=true ∨ i=1 ∨ i=3) → 0<(c.cell.weights i).lo)).1
  have hs : (0:ℝ)<ReferenceWeightData.CoarseLowerShape.scale := by norm_num [ReferenceWeightData.CoarseLowerShape.scale]
  have hb := (weights_contain hc hz i).1
  have hloR : (0:ℝ)≤(c.cell.weights i).lo := by exact_mod_cast hlo
  nlinarith
theorem weights_nonnegative {z : ℝ} (hz : z∈Ioc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish)
    (i : Fin 4) : 0≤weight i z := by
  obtain ⟨flow,hflow,_,hzflow,_⟩ := referenceField_selected ReferenceFlowCell.actualAlpha ReferenceWeightData.CoarseLowerShape.Assembly.cover_checked hz
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hflow
  exact weights_nonnegative_on_cell hc hzflow i
theorem weight_abs_bound {z : ℝ} (hz : z∈Ioc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish) (i : Fin 4) : |weight i z|≤20 := by
  obtain ⟨flow,hflow,_,hzflow,_⟩ := referenceField_selected ReferenceFlowCell.actualAlpha ReferenceWeightData.CoarseLowerShape.Assembly.cover_checked hz
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hflow
  have hbox : (c.cell.weights i).maxAbs≤20*ReferenceWeightData.CoarseLowerShape.scale := of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp ReferenceWeightData.CoarseLowerShape.Assembly.weight_bounds_checked c hc) i (List.mem_finRange i))
  have hb := IntegerInterval.abs_bound (by norm_num [ReferenceWeightData.CoarseLowerShape.scale]) (weights_contain hc hzflow i)
  have hs : (0:ℝ)<ReferenceWeightData.CoarseLowerShape.scale := by norm_num [ReferenceWeightData.CoarseLowerShape.scale]
  have hboxR : ((c.cell.weights i).maxAbs:ℝ)≤20*(ReferenceWeightData.CoarseLowerShape.scale:ℝ) := by exact_mod_cast hbox
  exact hb.trans ((div_le_iff₀ hs).mpr hboxR)
theorem first_member : ReferenceWeightData.CoarseLowerShape.Batch0000.cert0∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons_self,?_⟩
  exact List.mem_cons_self
theorem first_geometry : ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.left.z=ReferenceActualData.CoarseLowerShape.start ∧
    ReferenceActualData.CoarseLowerShape.start≤ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.z := by decide +kernel
theorem initial_value : Z ReferenceActualData.CoarseLowerShape.start=(ReferenceInitialAdjointData.CoarseLowerShape.initial:ℝ) := by
  rw [Z_spec.1,ReferenceInitialAdjointData.CoarseLowerShape.initial_linked]
  change cubicPrimitive ReferenceCurveData.CoarseLowerShape.tailLam ReferenceCurveData.CoarseLowerShape.tailSlack (ReferenceCurveData.CoarseLowerShape.piece0::_) ReferenceCurveData.CoarseLowerShape.piece0.lo=(ReferenceCurveData.CoarseLowerShape.piece0.f0:ℝ)
  exact trajectoryCheck_head_primitive ReferenceCurveData.CoarseLowerShape.assembly_checked
theorem initial_positive : 0<Z ReferenceActualData.CoarseLowerShape.start :=
  Z_spec.2.2.2.2 _ ⟨le_rfl,by norm_num [ReferenceActualData.CoarseLowerShape.start,ReferenceActualData.CoarseLowerShape.finish]⟩
end OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
