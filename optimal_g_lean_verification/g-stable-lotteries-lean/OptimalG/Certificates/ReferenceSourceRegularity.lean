import OptimalG.Certificates.ReferenceDensityMeasurable
import OptimalG.Certificates.HessianLogBound
import OptimalG.VariationalTransportSource

/-! The actual coefficient source is measurable on the reference interval.
A finite family of compact Hessian boxes supplies a uniform bound, so its
interval integral exists without a continuity assumption on the matching map. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory
open scoped BigOperators

theorem finite_cell_uniform_bound {I : Type*} (cells : List I)
    (region : I→Set ℝ) (f : ℝ→ℝ)
    (hc : ∀ c∈cells,∃ B : ℝ,0≤B ∧ ∀ z∈region c,|f z|≤B) :
    ∃ B : ℝ,0≤B ∧ ∀ c∈cells,∀ z∈region c,|f z|≤B := by
  induction cells with
  | nil => exact ⟨0,le_rfl,by simp⟩
  | cons c rest ih =>
    obtain ⟨B,hB,hcB⟩ := hc c List.mem_cons_self
    obtain ⟨C,hC,hrC⟩ := ih (fun d hd=>hc d (List.mem_cons_of_mem c hd))
    refine ⟨max B C,hB.trans (le_max_left _ _),?_⟩
    intro d hd z hz
    rcases List.mem_cons.mp hd with rfl | hd
    · exact (hcB z hz).trans (le_max_left _ _)
    · exact (hrC d hd z hz).trans (le_max_right _ _)

theorem transportCoefficientSource_measurable {I : Type*} [Fintype I]
    {rho w0 : ℝ→ℝ} {a a0 : ℝ→I→ℝ} (delta : I→ℝ)
    (hrho : Measurable rho) (hw0 : Measurable w0)
    (ha : ∀ i,Measurable (fun z=>a z i))
    (ha0 : ∀ i,Measurable (fun z=>a0 z i)) :
    Measurable (Variational.transportCoefficientSource rho w0 a a0 delta) := by
  apply hrho.mul
  apply Finset.measurable_sum
  intro i _
  have hm := ((ha0 i).mul
    (((measurable_const : Measurable (fun _ : ℝ => -delta i)).mul hw0).exp)).mul
      (Real.measurable_log.comp ((ha i).div (ha0 i)))
  convert hm using 1
  ext z
  simp [Variational.referenceWeight, Pi.mul_apply, Pi.div_apply, Function.comp_apply]

theorem transportCoefficientSource_aestronglyMeasurable {I : Type*} [Fintype I]
    {lo hi terminal : ℝ} (horder : lo≤hi) {Z E rho : ℝ→ℝ}
    (hZ : ContinuousOn Z (Icc lo hi)) (hE : ContinuousOn E (Icc lo hi))
    (hrho : ∀ z∈Icc lo hi,rho z=E z*Z z/terminal)
    {a a0 : ℝ→I→ℝ} (delta : I→ℝ)
    (ha : ∀ i,Measurable (fun z=>a z i))
    (ha0 : ∀ i,Measurable (fun z=>a0 z i)) :
    AEStronglyMeasurable
      (Variational.transportCoefficientSource rho (fun z=>Real.log (Z z)) a a0 delta)
      (volume.restrict (Ioc lo hi)) := by
  let Ze : ℝ→ℝ := fun z=>Z (referenceClamp lo hi z)
  let Ee : ℝ→ℝ := fun z=>E (referenceClamp lo hi z)
  have hmZ : Measurable Ze := (referenceClamp_comp_continuous horder hZ).measurable
  have hmE : Measurable Ee := (referenceClamp_comp_continuous horder hE).measurable
  have hm := transportCoefficientSource_measurable delta
    ((hmE.mul hmZ).div_const terminal) (Real.measurable_log.comp hmZ) ha ha0
  apply hm.aestronglyMeasurable.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with z hz
  have hzc : z∈Icc lo hi := ⟨hz.1.le,hz.2⟩
  simp only [Variational.transportCoefficientSource,Ze,Ee,Function.comp_apply,Pi.mul_apply,
    referenceClamp_eq hzc,hrho z hzc]

theorem transportCoefficientSource_intervalIntegrable {I : Type*} [Fintype I]
    {lo hi terminal B : ℝ} (horder : lo≤hi) {Z E rho : ℝ→ℝ}
    (hZ : ContinuousOn Z (Icc lo hi)) (hE : ContinuousOn E (Icc lo hi))
    (hrho : ∀ z∈Icc lo hi,rho z=E z*Z z/terminal)
    {a a0 : ℝ→I→ℝ} (delta : I→ℝ)
    (ha : ∀ i,Measurable (fun z=>a z i))
    (ha0 : ∀ i,Measurable (fun z=>a0 z i))
    (hb : ∀ z∈Ioc lo hi,
      |Variational.transportCoefficientSource rho (fun z=>Real.log (Z z)) a a0 delta z|≤B) :
    IntervalIntegrable
      (Variational.transportCoefficientSource rho (fun z=>Real.log (Z z)) a a0 delta)
      volume lo hi := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le horder).mpr
  apply (integrable_const B).mono'
    (transportCoefficientSource_aestronglyMeasurable horder hZ hE hrho delta ha ha0)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with z hz
  simpa only [Real.norm_eq_abs] using hb z hz

end OptimalG.Certificates.Transport
