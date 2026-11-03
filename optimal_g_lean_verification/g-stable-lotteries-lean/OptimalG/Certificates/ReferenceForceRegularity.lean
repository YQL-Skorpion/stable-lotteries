import OptimalG.Certificates.ReferenceDensityMeasurable

/-! Actual reference forces are measurable on the time interval even when
the chosen AC solution has no specified values outside that interval.
Finite interval bounds therefore imply genuine integrability. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

theorem referenceCoordinateForce_aestronglyMeasurable
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell) (cells : List ReferenceFlowCell)
    {a b : ℝ} (hab : a≤b) {Z E : ℝ→ℝ}
    (hZ : ContinuousOn Z (Icc a b)) (hE : ContinuousOn E (Icc a b))
    (terminal : ℝ) (j : Fin 16) :
    AEStronglyMeasurable (referenceCoordinateForce scalarFor cells Z E terminal j)
      (volume.restrict (Ioc a b)) := by
  have hm := referenceCoordinateForce_measurable scalarFor cells
    (referenceClamp_comp_continuous hab hZ).measurable
    (referenceClamp_comp_continuous hab hE).measurable terminal j
  apply hm.aestronglyMeasurable.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with z hz
  simp only [referenceCoordinateForce,Function.comp_apply,Pi.mul_apply,
    referenceClamp_eq ⟨hz.1.le,hz.2⟩]

theorem referenceCoordinateForce_intervalIntegrable
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell) (cells : List ReferenceFlowCell)
    {a b : ℝ} (hab : a≤b) {Z E : ℝ→ℝ}
    (hZ : ContinuousOn Z (Icc a b)) (hE : ContinuousOn E (Icc a b))
    (terminal : ℝ) (j : Fin 16) {B : ℝ}
    (hb : ∀ z∈Ioc a b,|referenceCoordinateForce scalarFor cells Z E terminal j z|≤B) :
    IntervalIntegrable (referenceCoordinateForce scalarFor cells Z E terminal j) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  apply (integrable_const B).mono'
    (referenceCoordinateForce_aestronglyMeasurable scalarFor cells hab hZ hE terminal j)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with z hz
  simpa only [Real.norm_eq_abs] using hb z hz

end OptimalG.Certificates.Transport
