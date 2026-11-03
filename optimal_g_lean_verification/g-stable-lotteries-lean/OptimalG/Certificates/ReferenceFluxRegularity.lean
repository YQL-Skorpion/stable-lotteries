import OptimalG.Certificates.ReferenceFluxPotential
import OptimalG.Certificates.ReferenceDensityMeasurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The finite flux checker supplies all integrability and positivity needed
by its integral budget once the genuine two densities are measurable. -/
namespace OptimalG.Certificates
open Set MeasureTheory

theorem cumulativeIntegralCheck_order {s : ℕ} {start finish : ℚ} {cells : List IntegralCell}
    (hc : cumulativeIntegralCheck s start finish cells=true) : start≤finish := by
  induction cells generalizing start with
  | nil => exact (of_decide_eq_true hc : start=finish).le
  | cons c cs ih =>
    have hh : (c.lo=start ∧ c.lo<c.hi) ∧ (totalBox cs).subsetCheck c.future=true ∧
        cumulativeIntegralCheck s c.hi finish cs=true := by
      simpa only [cumulativeIntegralCheck,Bool.and_eq_true,decide_eq_true_eq] using hc
    exact hh.1.1 ▸ hh.1.2.le.trans (ih hh.2.2)

theorem cumulativeIntegralCheck_cell_bounds {s : ℕ} {start finish : ℚ}
    {cells : List IntegralCell} (hc : cumulativeIntegralCheck s start finish cells=true)
    {c : IntegralCell} (hm : c∈cells) : start≤c.lo ∧ c.hi≤finish := by
  induction cells generalizing start with
  | nil => simp at hm
  | cons d ds ih =>
    have hh : (d.lo=start ∧ d.lo<d.hi) ∧ (totalBox ds).subsetCheck d.future=true ∧
        cumulativeIntegralCheck s d.hi finish ds=true := by
      simpa only [cumulativeIntegralCheck,Bool.and_eq_true,decide_eq_true_eq] using hc
    rcases List.mem_cons.mp hm with rfl|hm
    · exact ⟨hh.1.1.ge,cumulativeIntegralCheck_order hh.2.2⟩
    · have hb := ih hh.2.2 hm
      exact ⟨(hh.1.1 ▸ hh.1.2.le).trans hb.1,hb.2⟩

theorem cumulativeIntegralCheck_ae {s : ℕ} {start finish : ℚ} {cells : List IntegralCell}
    (hc : cumulativeIntegralCheck s start finish cells=true) {P : ℝ→Prop}
    (hp : ∀ c∈cells,∀ᵐ r ∂volume.restrict (Icc (c.lo:ℝ) c.hi),P r) :
    ∀ᵐ r ∂volume.restrict (Icc (start:ℝ) finish),P r := by
  induction cells generalizing start with
  | nil =>
    have he : start=finish := of_decide_eq_true hc
    simp [he]
  | cons c cs ih =>
    have hh : (c.lo=start ∧ c.lo<c.hi) ∧ (totalBox cs).subsetCheck c.future=true ∧
        cumulativeIntegralCheck s c.hi finish cs=true := by
      simpa only [cumulativeIntegralCheck,Bool.and_eq_true,decide_eq_true_eq] using hc
    have ht := ih hh.2.2 (fun d hd=>hp d (List.mem_cons_of_mem c hd))
    have hh' := hp c List.mem_cons_self
    have hs : (start:ℝ)≤c.hi := by exact_mod_cast (hh.1.1 ▸ hh.1.2.le)
    have hf : (c.hi:ℝ)≤finish := by exact_mod_cast cumulativeIntegralCheck_order hh.2.2
    have he : Icc (start:ℝ) finish=Icc (start:ℝ) c.hi ∪ Icc (c.hi:ℝ) finish := by
      ext r
      simp only [mem_Icc,mem_union]
      constructor
      · intro hr
        by_cases h : r≤(c.hi:ℝ)
        · exact Or.inl ⟨hr.1,h⟩
        · exact Or.inr ⟨(lt_of_not_ge h).le,hr.2⟩
      · rintro (hr|hr)
        · exact ⟨hr.1,hr.2.trans hf⟩
        · exact ⟨hs.trans hr.1,hr.2⟩
    rw [he,ae_restrict_union_iff]
    exact ⟨by simpa only [hh.1.1] using hh',ht⟩

namespace Transport.ReferenceFluxCell

theorem checked_measurable_flux_budget {s k : ℕ} (hs : 0<s) (hk : 0<k)
    {start finish flux budget : ℚ} (cells : List ReferenceFluxCell)
    (hchecks : cells.all (fun c=>c.check s k)=true)
    (hcover : cumulativeIntegralCheck s start finish (cells.map (·.interval))=true)
    (hflux : cells.all (fun c=>decide (c.flux=flux))=true)
    (hbudget : errorBudgetCheck s budget cells=true)
    {f W : ℝ→ℝ} (hf : Measurable f) (hW : Measurable W)
    (hpw : ∀ c∈cells,∀ r∈Ioo (c.interval.lo:ℝ) c.interval.hi,
      c.position.Contains s (f r) ∧ c.weight.Contains s (W r)) :
    IntervalIntegrable f volume (start:ℝ) finish ∧
    (∀ᵐ r ∂volume.restrict (Icc (start:ℝ) finish),
      3≤W r ∧ 0<(∫ x in r..(finish:ℝ),f x)-flux-3) ∧
    (∫ r in (start:ℝ)..finish,
      ((∫ x in r..(finish:ℝ),f x)-W r-flux)^2/
        ((∫ x in r..(finish:ℝ),f x)-flux-3))<(budget:ℝ) := by
  have hbound (c : ReferenceFluxCell) (hc : c∈cells) :
      ∀ᵐ r ∂volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi),
        c.position.Contains s (f r) ∧ c.weight.Contains s (W r) := by
    rw [←restrict_Ioo_eq_restrict_Icc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with r hr
    exact hpw c hc r hr
  have hpos := fun c hc=>(hbound c hc).mono (fun _ hr=>hr.1)
  have hweight := fun c hc=>(hbound c hc).mono (fun _ hr=>hr.2)
  obtain ⟨hfi,hpotential⟩ := checked_actual_potential hs hk cells hchecks hcover
    (fun _ _=>hf.aestronglyMeasurable) hpos hweight
  have horder : (start:ℝ)≤finish := by exact_mod_cast cumulativeIntegralCheck_order hcover
  have hP : ContinuousOn (fun r=>∫ x in r..(finish:ℝ),f x) (Icc (start:ℝ) finish) := by
    simpa only [uIcc_of_le horder] using
      intervalIntegral.continuousOn_primitive_interval_left ((intervalIntegrable_iff').mp hfi)
  have hPm := (referenceClamp_comp_continuous horder hP).measurable
  have he (c : ReferenceFluxCell) (hc : c∈cells) :
      AEStronglyMeasurable
      (fun r=>((∫ x in r..(finish:ℝ),f x)-W r-flux)^2/
        ((∫ x in r..(finish:ℝ),f x)-flux-3))
      (volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi)) := by
    have hb := cumulativeIntegralCheck_cell_bounds hcover (List.mem_map.mpr ⟨c,hc,rfl⟩)
    have hfm : Measurable (fun _ : ℝ=>(flux:ℝ)) := measurable_const
    have hthree : Measurable (fun _ : ℝ=>(3:ℝ)) := measurable_const
    apply ((((hPm.sub hW).sub hfm).pow_const 2).div
      ((hPm.sub hfm).sub hthree)).aestronglyMeasurable.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with r hr
    have hr' : r∈Icc (start:ℝ) finish :=
      ⟨(show (start:ℝ)≤c.interval.lo by exact_mod_cast hb.1).trans hr.1,
        hr.2.trans (by exact_mod_cast hb.2)⟩
    simp only [Pi.div_apply,Pi.sub_apply,Pi.pow_apply,referenceClamp_eq hr']
  refine ⟨hfi,?_,(checked_actual_flux_budget hs hk cells hchecks hcover hflux hbudget
    (fun _ _=>hf.aestronglyMeasurable) hpos hweight he).2⟩
  apply cumulativeIntegralCheck_ae hcover
  intro d hd
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd
  have heq : c.flux=flux := of_decide_eq_true (List.all_eq_true.mp hflux c hc)
  filter_upwards [hpotential c hc] with r hr
  exact ⟨hr.2.1,by simpa only [heq] using hr.2.2.1⟩

end Transport.ReferenceFluxCell
end OptimalG.Certificates
