import OptimalG.Certificates.ReferenceFluxAssembly
import OptimalG.Certificates.ExpressionTaylorResidual

/-! Cumulative finite checks are applied to the genuine positional potential.
Measurability and accepted pointwise intervals imply the integrability needed
by the flux absorption estimate; no suffix integral is assumed independently.
-/
namespace OptimalG.Certificates
open Set MeasureTheory
namespace IntegerInterval

theorem intervalIntegrable_of_ae_contains {s : ℕ} (hs : 0<s)
    {a b : ℝ} (hab : a≤b) {box : IntegerInterval} {f : ℝ→ℝ}
    (hm : AEStronglyMeasurable f (volume.restrict (Icc a b)))
    (hb : ∀ᵐ r ∂volume.restrict (Icc a b),box.Contains s (f r)) :
    IntervalIntegrable f volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  apply (integrable_const ((box.maxAbs:ℝ)/(s:ℝ))).mono' hm
  filter_upwards [hb] with r hr
  simpa only [Real.norm_eq_abs] using abs_bound hs hr

end IntegerInterval
namespace Transport.ReferenceFluxCell

theorem checked_actual_potential {s k : ℕ} (hs : 0<s) (hk : 0<k)
    {start finish : ℚ} (cells : List ReferenceFluxCell)
    (hchecks : cells.all (fun c=>c.check s k)=true)
    (hcover : cumulativeIntegralCheck s start finish (cells.map (·.interval))=true)
    {f W : ℝ→ℝ}
    (hm : ∀ c∈cells,AEStronglyMeasurable f
      (volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi)))
    (hp : ∀ c∈cells,∀ᵐ r ∂volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi),
      c.position.Contains s (f r))
    (hw : ∀ c∈cells,∀ᵐ r ∂volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi),
      c.weight.Contains s (W r)) :
    IntervalIntegrable f volume (start:ℝ) finish ∧
      ∀ c∈cells,∀ᵐ r ∂volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi),
        c.potential.Contains s (∫ x in r..(finish:ℝ),f x) ∧ 3≤W r ∧
        0<(∫ x in r..(finish:ℝ),f x)-c.flux-3 ∧
        c.error.Contains s (((∫ x in r..(finish:ℝ),f x)-W r-c.flux)^2/
          ((∫ x in r..(finish:ℝ),f x)-c.flux-3)) := by
  have hlocal (c : ReferenceFluxCell) (hc : c∈cells) :
      IntervalIntegrable f volume (c.interval.lo:ℝ) c.interval.hi := by
    have horder := cumulativeIntegralCheck_cell_order hcover (List.mem_map.mpr ⟨c,hc,rfl⟩)
    exact IntegerInterval.intervalIntegrable_of_ae_contains hs (by exact_mod_cast horder.le)
      (hm c hc) (hp c hc)
  have hsum := cumulativeIntegralCheck_sound hcover (fun d hd=>by
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd
    exact ⟨hlocal c hc,c.checked_position_mass hs (List.all_eq_true.mp hchecks c hc)
      (cumulativeIntegralCheck_cell_order hcover (List.mem_map.mpr ⟨c,hc,rfl⟩)).le
      (hlocal c hc) (hp c hc)⟩)
  refine ⟨hsum.1,?_⟩
  intro c hc
  have hfuture := hsum.2.2 c.interval (List.mem_map.mpr ⟨c,hc,rfl⟩)
  filter_upwards [self_mem_ae_restrict measurableSet_Icc,hw c hc] with r hr hwr
  exact c.checked_potential_error hs hk (List.all_eq_true.mp hchecks c hc) hr
    (hlocal c hc) hfuture.1 (hp c hc) hfuture.2 hwr

theorem checked_actual_flux_budget {s k : ℕ} (hs : 0<s) (hk : 0<k)
    {start finish flux budget : ℚ} (cells : List ReferenceFluxCell)
    (hchecks : cells.all (fun c=>c.check s k)=true)
    (hcover : cumulativeIntegralCheck s start finish (cells.map (·.interval))=true)
    (hflux : cells.all (fun c=>decide (c.flux=flux))=true)
    (hbudget : errorBudgetCheck s budget cells=true)
    {f W : ℝ→ℝ}
    (hm : ∀ c∈cells,AEStronglyMeasurable f
      (volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi)))
    (hp : ∀ c∈cells,∀ᵐ r ∂volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi),
      c.position.Contains s (f r))
    (hw : ∀ c∈cells,∀ᵐ r ∂volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi),
      c.weight.Contains s (W r))
    (he : ∀ c∈cells,AEStronglyMeasurable
      (fun r=>((∫ x in r..(finish:ℝ),f x)-W r-flux)^2/
        ((∫ x in r..(finish:ℝ),f x)-flux-3))
      (volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi))) :
    IntervalIntegrable f volume (start:ℝ) finish ∧
    (∫ r in (start:ℝ)..finish,
      ((∫ x in r..(finish:ℝ),f x)-W r-flux)^2/
        ((∫ x in r..(finish:ℝ),f x)-flux-3))<(budget:ℝ) := by
  obtain ⟨hfi,hbound⟩ := checked_actual_potential hs hk cells hchecks hcover hm hp hw
  have herr (c : ReferenceFluxCell) (hc : c∈cells) :
      ∀ᵐ r ∂volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi),
        c.error.Contains s (((∫ x in r..(finish:ℝ),f x)-W r-flux)^2/
          ((∫ x in r..(finish:ℝ),f x)-flux-3)) := by
    have hf : c.flux=flux := of_decide_eq_true (List.all_eq_true.mp hflux c hc)
    filter_upwards [hbound c hc] with r hr
    simpa only [hf] using hr.2.2.2
  refine ⟨hfi,(checked_error_budget hs cells hchecks hcover hbudget ?_ herr).2⟩
  intro c hc
  have ho := cumulativeIntegralCheck_cell_order hcover (List.mem_map.mpr ⟨c,hc,rfl⟩)
  exact IntegerInterval.intervalIntegrable_of_ae_contains hs (by exact_mod_cast ho.le)
    (he c hc) (herr c hc)

end Transport.ReferenceFluxCell
end OptimalG.Certificates
