import OptimalG.Certificates.ReferenceFlowPartition

/-! Almost-everywhere statements on the genuine checked time cells glue to
one statement on the whole reference interval, retaining all finite joins. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

theorem referenceFlowCoverCheck_ae_Ioc {start finish : ℚ} {cells : List ReferenceFlowCell}
    {P : ℝ→Prop} (hc : referenceFlowCoverCheck start finish cells=true)
    (hcell : ∀ c∈cells,∀ᵐ z ∂volume.restrict (Ioc (c.segment.left.z:ℝ) c.segment.right.z),P z) :
    ∀ᵐ z ∂volume.restrict (Ioc (start:ℝ) finish),P z := by
  induction cells generalizing start with
  | nil =>
    have he : start=finish := of_decide_eq_true hc
    subst start
    simp
  | cons c cs ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    have h : c.segment.left.z=start ∧ c.segment.left.z<c.segment.right.z :=
      of_decide_eq_true hh.1
    have hfirst := hcell c List.mem_cons_self
    have htail := ih hh.2 (fun d hd=>hcell d (List.mem_cons_of_mem c hd))
    rw [h.1] at hfirst
    have hlo : (start:ℝ)≤c.segment.right.z := by exact_mod_cast (h.1 ▸ h.2.le)
    have hhi : (c.segment.right.z:ℝ)≤finish := by
      exact_mod_cast referenceFlowCoverCheck_order hh.2
    rw [←Ioc_union_Ioc_eq_Ioc hlo hhi,ae_restrict_union_iff]
    exact ⟨hfirst,htail⟩

theorem referenceFlowCoverCheck_ae {start finish : ℚ} {cells : List ReferenceFlowCell}
    {P : ℝ→Prop} (hc : referenceFlowCoverCheck start finish cells=true)
    (hcell : ∀ c∈cells,∀ᵐ z ∂volume.restrict (Icc (c.segment.left.z:ℝ) c.segment.right.z),P z) :
    ∀ᵐ z ∂volume.restrict (Icc (start:ℝ) finish),P z := by
  rw [←Measure.restrict_congr_set Ioc_ae_eq_Icc]
  apply referenceFlowCoverCheck_ae_Ioc hc
  intro c hm
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
  exact hcell c hm

/-- A locally established relation involving any finite family of selected
reference fields becomes a global a.e. relation, without postulating branch
selection or excluding each join separately. -/
theorem referenceFields_ae {I : Type*} {start finish : ℚ}
    {cells : List ReferenceFlowCell} (field : I→ReferenceFlowCell→ℝ→ℝ)
    {P : ℝ→(I→ℝ)→Prop} (hc : referenceFlowCoverCheck start finish cells=true)
    (hcell : ∀ c∈cells,∀ᵐ z ∂volume.restrict (Icc (c.segment.left.z:ℝ) c.segment.right.z),
      P z (fun i=>field i c (c.timeParameter z))) :
    ∀ᵐ z ∂volume.restrict (Icc (start:ℝ) finish),
      P z (fun i=>referenceField (field i) cells z) := by
  rw [←Measure.restrict_congr_set Ioc_ae_eq_Icc]
  apply referenceFlowCoverCheck_ae_Ioc hc
  intro c hm
  have hlocal := hcell c hm
  rw [←Measure.restrict_congr_set Ioc_ae_eq_Icc] at hlocal
  filter_upwards [hlocal,ae_restrict_mem measurableSet_Ioc] with z hz hzi
  have he : (fun i=>referenceField (field i) cells z)=
      (fun i=>field i c (c.timeParameter z)) := by
    funext i
    exact referenceField_on_cell (field i) hc hm hzi
  rwa [he]

end OptimalG.Certificates.Transport
