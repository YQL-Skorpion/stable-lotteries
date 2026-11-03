import OptimalG.Certificates.ReferenceFlowField

/-! Exact selection and integration on a checked reference time partition. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

theorem referenceFlowCoverCheck_order {start finish : ℚ} {cells : List ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish cells=true) : start≤finish := by
  induction cells generalizing start with
  | nil => exact le_of_eq (of_decide_eq_true hc)
  | cons c cs ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    have h : c.segment.left.z=start ∧ c.segment.left.z<c.segment.right.z := of_decide_eq_true hh.1
    exact (h.1 ▸ h.2.le).trans (ih hh.2)

theorem referenceFlowCoverCheck_bounds {start finish : ℚ} {cells : List ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish cells=true) {c : ReferenceFlowCell} (hm : c∈cells) :
    start≤c.segment.left.z ∧ c.segment.left.z<c.segment.right.z ∧ c.segment.right.z≤finish := by
  induction cells generalizing start with
  | nil => simp at hm
  | cons d ds ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    have h : d.segment.left.z=start ∧ d.segment.left.z<d.segment.right.z := of_decide_eq_true hh.1
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨h.1.symm.le,h.2,referenceFlowCoverCheck_order hh.2⟩
    · have ht := ih hh.2 hm
      exact ⟨(h.1 ▸ h.2.le).trans ht.1,ht.2⟩

theorem referenceField_on_cell (field : ReferenceFlowCell→ℝ→ℝ)
    {start finish : ℚ} {cells : List ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish cells=true) {c : ReferenceFlowCell} (hm : c∈cells)
    {z : ℝ} (hz : z∈Ioc (c.segment.left.z:ℝ) c.segment.right.z) :
    referenceField field cells z=field c (c.timeParameter z) := by
  induction cells generalizing start with
  | nil => simp at hm
  | cons d ds ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    rcases List.mem_cons.mp hm with rfl | hm
    · simp only [referenceField,if_pos hz.2]
    · have hstart := (referenceFlowCoverCheck_bounds hh.2 hm).1
      have hcast : (d.segment.right.z:ℝ)≤c.segment.left.z := by exact_mod_cast hstart
      have hnot : ¬z≤(d.segment.right.z:ℝ) := not_le.mpr (hcast.trans_lt hz.1)
      simpa only [referenceField,if_neg hnot] using ih hh.2 hm

theorem referenceField_cell_integral (field : ReferenceFlowCell→ℝ→ℝ)
    {start finish : ℚ} {cells : List ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish cells=true) {c : ReferenceFlowCell} (hm : c∈cells) :
    (∫ z in (c.segment.left.z:ℝ)..c.segment.right.z,referenceField field cells z)=
      (c.length:ℝ)*(∫ t in (0:ℝ)..1,field c t) := by
  have hpos := (referenceFlowCoverCheck_bounds hc hm).2.1
  have hpos' : (c.segment.left.z:ℝ)<c.segment.right.z := by exact_mod_cast hpos
  have hlen : (c.length:ℝ)≠0 := by
    exact_mod_cast (sub_ne_zero.mpr hpos.ne' : c.segment.right.z-c.segment.left.z≠0)
  calc
    _=∫ z in (c.segment.left.z:ℝ)..c.segment.right.z,field c ((z-c.segment.left.z)/(c.length:ℝ)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hpos'.le
      intro z hz
      exact referenceField_on_cell field hc hm ⟨hz.1,hz.2.le⟩
    _=_ := by
      rw [intervalIntegral.integral_comp_sub_right
        (fun t : ℝ=>field c (t/(c.length:ℝ))) (c.segment.left.z:ℝ),
        intervalIntegral.integral_comp_div _ hlen]
      have hsub : ((c.segment.right.z:ℝ)-c.segment.left.z)=(c.length:ℝ) := by
        simp only [ReferenceFlowCell.length,Rat.cast_sub]
      simp only [sub_self,zero_div,hsub,div_self hlen,smul_eq_mul]

theorem referenceFlow_partition_integral (f : ℝ→ℝ)
    {start finish : ℚ} {cells : List ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish cells=true)
    (hi : ∀ c∈cells,IntervalIntegrable f volume (c.segment.left.z:ℝ) c.segment.right.z) :
    IntervalIntegrable f volume (start:ℝ) finish ∧
      (∫ z in (start:ℝ)..finish,f z)=
        (cells.map (fun c => ∫ z in (c.segment.left.z:ℝ)..c.segment.right.z,f z)).sum := by
  induction cells generalizing start with
  | nil =>
    have he : start=finish := of_decide_eq_true hc
    subst start
    exact ⟨IntervalIntegrable.refl,by simp⟩
  | cons c cs ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    have h : c.segment.left.z=start ∧ c.segment.left.z<c.segment.right.z := of_decide_eq_true hh.1
    have hfirst := hi c List.mem_cons_self
    have htail := ih hh.2 (fun d hd => hi d (List.mem_cons_of_mem c hd))
    rw [h.1] at hfirst
    refine ⟨hfirst.trans htail.1,?_⟩
    rw [←intervalIntegral.integral_add_adjacent_intervals hfirst htail.1,htail.2]
    simp only [List.map_cons,List.sum_cons,h.1]

end OptimalG.Certificates.Transport
