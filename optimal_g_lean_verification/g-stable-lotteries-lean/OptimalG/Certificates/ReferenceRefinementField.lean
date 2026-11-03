import OptimalG.Certificates.ReferenceRefinement

/-! Refined quadrature cells use the same actual piecewise affine field as
the coarse residual-certified ODE. Half-open selection includes all shared
right endpoints and avoids any discontinuity premise at a join. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory
namespace ReferenceFlowCell

theorem refinement_time_geometry {parent child : ReferenceFlowCell} {lo hi : ℚ}
    (hc : parent.refinementCheck child lo hi=true)
    (hp : parent.segment.left.z<parent.segment.right.z) :
    child.segment.left.z<child.segment.right.z ∧
      parent.segment.left.z≤child.segment.left.z ∧
      child.segment.right.z≤parent.segment.right.z ∧
      ∀ z : ℝ,parent.timeParameter z=
        (lo:ℝ)+(hi-lo)*child.timeParameter z := by
  have h : child.lam=parent.lam ∧ child.slack=parent.slack ∧ child.level=parent.level ∧
      child.late=parent.late ∧ child.rPiece=parent.rPiece ∧ child.aPiece=parent.aPiece ∧
      child.segment.left=parent.interpolateNode lo ∧ child.segment.right=parent.interpolateNode hi ∧
      0≤lo ∧ lo<hi ∧ hi≤1 := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
  rcases h with ⟨_,_,_,_,_,_,hlft,hrgt,hlo,hlt,hhi⟩
  have hl : child.segment.left.z=parent.segment.left.z+
      (parent.segment.right.z-parent.segment.left.z)*lo := by rw [hlft]; rfl
  have hr : child.segment.right.z=parent.segment.left.z+
      (parent.segment.right.z-parent.segment.left.z)*hi := by rw [hrgt]; rfl
  have hlen : 0<parent.length := sub_pos.mpr hp
  have hchild : child.length=parent.length*(hi-lo) := by
    unfold length
    rw [hl,hr]
    ring
  have hcpos : 0<child.length := by rw [hchild]; exact mul_pos hlen (sub_pos.mpr hlt)
  refine ⟨sub_pos.mp hcpos,?_,?_,?_⟩
  · rw [hl]
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hp.le) hlo)
  · rw [hr]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hp.le) (sub_nonneg.mpr hhi)]
  · intro z
    have hplen : (parent.length:ℝ)≠0 := by exact_mod_cast hlen.ne'
    have hdelta : (hi:ℝ)-(lo:ℝ)≠0 := by exact_mod_cast (sub_ne_zero.mpr hlt.ne')
    unfold timeParameter
    rw [hchild,hl]
    push_cast
    have hplenEq : (parent.length:ℝ)=
        (parent.segment.right.z:ℝ)-parent.segment.left.z := by simp only [length,Rat.cast_sub]
    rw [←hplenEq]
    field_simp [hplen,hdelta]
    <;> ring

theorem refinement_mem_parent {parent child : ReferenceFlowCell} {lo hi : ℚ}
    (hc : parent.refinementCheck child lo hi=true)
    (hp : parent.segment.left.z<parent.segment.right.z) {z : ℝ}
    (hz : z∈Ioc (child.segment.left.z:ℝ) child.segment.right.z) :
    z∈Ioc (parent.segment.left.z:ℝ) parent.segment.right.z := by
  have hh := refinement_time_geometry hc hp
  have hl : (parent.segment.left.z:ℝ)≤child.segment.left.z := by exact_mod_cast hh.2.1
  have hr : (child.segment.right.z:ℝ)≤parent.segment.right.z := by exact_mod_cast hh.2.2.1
  exact ⟨hl.trans_lt hz.1,hz.2.trans hr⟩

end ReferenceFlowCell

theorem referenceField_on_refined_cell {start finish lo hi : ℚ}
    {cells : List ReferenceFlowCell} {parent child : ReferenceFlowCell}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : parent∈cells)
    (href : parent.refinementCheck child lo hi=true) {z : ℝ}
    (hz : z∈Ioc (child.segment.left.z:ℝ) child.segment.right.z) :
    referenceField ReferenceFlowCell.actualAlpha cells z=child.actualAlpha (child.timeParameter z) ∧
      referenceField ReferenceFlowCell.actualBeta cells z=child.actualBeta (child.timeParameter z) := by
  have hp := (referenceFlowCoverCheck_bounds hcover hmem).2.1
  have hzp := ReferenceFlowCell.refinement_mem_parent href hp hz
  have ht := (ReferenceFlowCell.refinement_time_geometry href hp).2.2.2 z
  have hf := ReferenceFlowCell.refinementCheck_fields href (child.timeParameter z)
  rw [referenceField_on_cell ReferenceFlowCell.actualAlpha hcover hmem hzp,
    referenceField_on_cell ReferenceFlowCell.actualBeta hcover hmem hzp,ht]
  exact ⟨hf.2.2.2.1.symm,hf.2.2.2.2.1.symm⟩

theorem referenceField_refined_alpha_integral {start finish lo hi : ℚ}
    {cells : List ReferenceFlowCell} {parent child : ReferenceFlowCell}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : parent∈cells)
    (href : parent.refinementCheck child lo hi=true) :
    (∫ z in (child.segment.left.z:ℝ)..child.segment.right.z,
      referenceField ReferenceFlowCell.actualAlpha cells z)=
      (child.length:ℝ)*(∫ t in (0:ℝ)..1,child.actualAlpha t) := by
  have hpos := (ReferenceFlowCell.refinement_time_geometry href
    (referenceFlowCoverCheck_bounds hcover hmem).2.1).1
  have hpos' : (child.segment.left.z:ℝ)<child.segment.right.z := by exact_mod_cast hpos
  have hlen : (child.length:ℝ)≠0 := by
    exact_mod_cast (sub_ne_zero.mpr hpos.ne' : child.segment.right.z-child.segment.left.z≠0)
  calc
    _=∫ z in (child.segment.left.z:ℝ)..child.segment.right.z,
        child.actualAlpha ((z-child.segment.left.z)/(child.length:ℝ)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hpos'.le
      intro z hz
      exact (referenceField_on_refined_cell hcover hmem href ⟨hz.1,hz.2.le⟩).1
    _=_ := by
      rw [intervalIntegral.integral_comp_sub_right
        (fun t : ℝ=>child.actualAlpha (t/(child.length:ℝ))) (child.segment.left.z:ℝ),
        intervalIntegral.integral_comp_div _ hlen]
      have hsub : ((child.segment.right.z:ℝ)-child.segment.left.z)=(child.length:ℝ) := by
        simp only [ReferenceFlowCell.length,Rat.cast_sub]
      simp only [sub_self,zero_div,hsub,div_self hlen,smul_eq_mul]

theorem referenceField_refined_beta_integral {start finish lo hi : ℚ}
    {cells : List ReferenceFlowCell} {parent child : ReferenceFlowCell}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : parent∈cells)
    (href : parent.refinementCheck child lo hi=true) :
    (∫ z in (child.segment.left.z:ℝ)..child.segment.right.z,
      referenceField ReferenceFlowCell.actualBeta cells z)=
      (child.length:ℝ)*(∫ t in (0:ℝ)..1,child.actualBeta t) := by
  have hpos := (ReferenceFlowCell.refinement_time_geometry href
    (referenceFlowCoverCheck_bounds hcover hmem).2.1).1
  have hpos' : (child.segment.left.z:ℝ)<child.segment.right.z := by exact_mod_cast hpos
  have hlen : (child.length:ℝ)≠0 := by
    exact_mod_cast (sub_ne_zero.mpr hpos.ne' : child.segment.right.z-child.segment.left.z≠0)
  calc
    _=∫ z in (child.segment.left.z:ℝ)..child.segment.right.z,
        child.actualBeta ((z-child.segment.left.z)/(child.length:ℝ)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hpos'.le
      intro z hz
      exact (referenceField_on_refined_cell hcover hmem href ⟨hz.1,hz.2.le⟩).2
    _=_ := by
      rw [intervalIntegral.integral_comp_sub_right
        (fun t : ℝ=>child.actualBeta (t/(child.length:ℝ))) (child.segment.left.z:ℝ),
        intervalIntegral.integral_comp_div _ hlen]
      have hsub : ((child.segment.right.z:ℝ)-child.segment.left.z)=(child.length:ℝ) := by
        simp only [ReferenceFlowCell.length,Rat.cast_sub]
      simp only [sub_self,zero_div,hsub,div_self hlen,smul_eq_mul]

end OptimalG.Certificates.Transport
