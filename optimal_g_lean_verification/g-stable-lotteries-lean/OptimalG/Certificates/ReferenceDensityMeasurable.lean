import OptimalG.Certificates.ReferenceDensityAssembly
import OptimalG.Certificates.ReferenceCoordinateForce

/-! Measurability of the genuine reference densities only uses regularity on
the finite reference time interval. Values of the chosen AC solution outside
that interval never enter a density supported by a checked segment. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

noncomputable def referenceClamp (a b z : ℝ) : ℝ := max a (min b z)

theorem referenceClamp_mem {a b : ℝ} (hab : a≤b) (z : ℝ) :
    referenceClamp a b z∈Icc a b :=
  ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩

theorem referenceClamp_eq {a b z : ℝ} (hz : z∈Icc a b) :
    referenceClamp a b z=z := by
  simp only [referenceClamp,min_eq_right hz.2,max_eq_right hz.1]

theorem referenceClamp_continuous (a b : ℝ) : Continuous (referenceClamp a b) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem referenceClamp_comp_continuous {a b : ℝ} (hab : a≤b) {f : ℝ→ℝ}
    (hf : ContinuousOn f (Icc a b)) : Continuous (fun z=>f (referenceClamp a b z)) :=
  hf.comp_continuous (referenceClamp_continuous a b) (referenceClamp_mem hab)

theorem segmentDensity_measurable (seg : ReferenceSegment) (rank : ReferenceNode→ℚ)
    {weight : ℝ→ℝ} (hw : Measurable weight) : Measurable (segmentDensity seg rank weight) := by
  have hi : Measurable (seg.inverseRankMap rank) := by
    exact measurable_const.add ((measurable_id.sub measurable_const).div_const _)
  exact Measurable.ite measurableSet_Ioo ((hw.comp hi).div_const _) measurable_const

theorem segmentDensity_congr_on_time {seg : ReferenceSegment} {rank : ReferenceNode→ℚ}
    (htime : seg.left.z<seg.right.z) {w v : ℝ→ℝ}
    (he : ∀ z∈Icc (seg.left.z:ℝ) seg.right.z,w z=v z) :
    segmentDensity seg rank w=segmentDensity seg rank v := by
  funext r
  by_cases hr : r∈Ioo (rank seg.left:ℝ) (rank seg.right:ℝ)
  · have horder : rank seg.left<rank seg.right := by exact_mod_cast hr.1.trans hr.2
    have hslope : 0<seg.slope rank := div_pos (sub_pos.mpr horder) (sub_pos.mpr htime)
    have hz := ReferenceSegment.inverseRankMap_mem htime hslope hr
    simp only [segmentDensity,if_pos hr,he _ ⟨hz.1.le,hz.2.le⟩]
  · simp only [segmentDensity,if_neg hr]

theorem segmentDensity_measurable_of_extension {seg : ReferenceSegment}
    {rank : ReferenceNode→ℚ} {a b : ℝ} (htime : seg.left.z<seg.right.z)
    (hlo : a≤(seg.left.z:ℝ)) (hhi : (seg.right.z:ℝ)≤b)
    {weight extension : ℝ→ℝ} (hm : Measurable extension)
    (he : ∀ z∈Icc a b,weight z=extension z) :
    Measurable (segmentDensity seg rank weight) := by
  rw [segmentDensity_congr_on_time htime (fun z hz=>he z ⟨hlo.trans hz.1,hz.2.trans hhi⟩)]
  exact segmentDensity_measurable seg rank hm

theorem coordinateForce_density_measurable
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell) (cells : List ReferenceFlowCell)
    {a b : ℝ} (hab : a≤b) {Z E : ℝ→ℝ}
    (hZ : ContinuousOn Z (Icc a b)) (hE : ContinuousOn E (Icc a b))
    (terminal : ℝ) (j : Fin 16) {seg : ReferenceSegment} (rank : ReferenceNode→ℚ)
    (htime : seg.left.z<seg.right.z) (hlo : a≤(seg.left.z:ℝ))
    (hhi : (seg.right.z:ℝ)≤b) :
    Measurable (segmentDensity seg rank
      (referenceCoordinateForce scalarFor cells Z E terminal j)) := by
  apply segmentDensity_measurable_of_extension htime hlo hhi
    (referenceCoordinateForce_measurable scalarFor cells
      (referenceClamp_comp_continuous hab hZ).measurable
      (referenceClamp_comp_continuous hab hE).measurable terminal j)
  intro z hz
  simp only [referenceCoordinateForce,referenceClamp_eq hz]

theorem adjointWeight_density_measurable {a b : ℝ} (hab : a≤b)
    {Z E coefficient weight : ℝ→ℝ}
    (hZ : ContinuousOn Z (Icc a b)) (hE : ContinuousOn E (Icc a b))
    (hc : Measurable coefficient) (terminal : ℝ) (i : Fin 4)
    (he : ∀ z∈Icc a b,weight z=(E z/terminal)*(if i.val<2 then Z z else 1)*coefficient z)
    {seg : ReferenceSegment} (rank : ReferenceNode→ℚ)
    (htime : seg.left.z<seg.right.z) (hlo : a≤(seg.left.z:ℝ))
    (hhi : (seg.right.z:ℝ)≤b) : Measurable (segmentDensity seg rank weight) := by
  have hz := (referenceClamp_comp_continuous hab hZ).measurable
  have hex := (referenceClamp_comp_continuous hab hE).measurable
  have hp : Measurable (fun z=>if i.val<2 then Z (referenceClamp a b z) else 1) := by
    split_ifs <;> first | exact hz | exact measurable_const
  apply segmentDensity_measurable_of_extension htime hlo hhi
    (((hex.div_const terminal).mul hp).mul hc)
  intro z hzm
  simpa only [Pi.mul_apply,referenceClamp_eq hzm] using he z hzm

theorem segmentDensity_add (seg : ReferenceSegment) (rank : ReferenceNode→ℚ)
    (v w : ℝ→ℝ) : segmentDensity seg rank (fun z=>v z+w z)=
      fun r=>segmentDensity seg rank v r+segmentDensity seg rank w r := by
  funext r
  by_cases hr : r∈Ioo (rank seg.left:ℝ) (rank seg.right:ℝ)
  · simp only [segmentDensity,if_pos hr,add_div]
  · simp only [segmentDensity,if_neg hr,add_zero]

theorem pushforwardDensity_measurable {segments : List ReferenceSegment}
    (rank : ReferenceNode→ℚ) (weight : ReferenceSegment→ℝ→ℝ)
    (hm : ∀ seg∈segments,Measurable (segmentDensity seg rank (weight seg))) :
    Measurable (pushforwardDensity segments rank weight) := by
  induction segments with
  | nil => exact measurable_const
  | cons seg rest ih =>
    have hr := ih (fun s hs=>hm s (List.mem_cons_of_mem seg hs))
    exact (hm seg List.mem_cons_self).add hr

end OptimalG.Certificates.Transport
