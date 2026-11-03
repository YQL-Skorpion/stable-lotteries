import OptimalG.Certificates.ReferenceFluxRegularity
import OptimalG.VariationalStieltjesIntegrability

/-! Closed cumulative enclosures control the potential at every rank,
including endpoints carrying singular matching mass. Uniform finite bounds
also discharge all error-integrability hypotheses of Stieltjes coercivity. -/
namespace OptimalG.Certificates
open Set MeasureTheory

theorem cumulativeIntegralCheck_cover {s : ℕ} {start finish : ℚ}
    {cells : List IntegralCell} (ho : start<finish)
    (hc : cumulativeIntegralCheck s start finish cells=true)
    {r : ℝ} (hr : r∈Icc (start:ℝ) finish) :
    ∃ c∈cells,r∈Icc (c.lo:ℝ) c.hi := by
  induction cells generalizing start with
  | nil =>
    have he : start=finish := of_decide_eq_true hc
    exact False.elim (ho.ne he)
  | cons c cs ih =>
    have hh : (c.lo=start ∧ c.lo<c.hi) ∧ (totalBox cs).subsetCheck c.future=true ∧
        cumulativeIntegralCheck s c.hi finish cs=true := by
      simpa only [cumulativeIntegralCheck,Bool.and_eq_true,decide_eq_true_eq] using hc
    by_cases h : r≤(c.hi:ℝ)
    · exact ⟨c,List.mem_cons_self,by simpa only [hh.1.1,mem_Icc] using And.intro hr.1 h⟩
    · have hlo : (c.hi:ℝ)<r := lt_of_not_ge h
      have horder : c.hi<finish := by exact_mod_cast hlo.trans_le hr.2
      obtain ⟨d,hd,hdr⟩ := ih horder hh.2.2 ⟨hlo.le,hr.2⟩
      exact ⟨d,List.mem_cons_of_mem c hd,hdr⟩

private theorem finite_uniform_upper {α : Type*} (cells : List α) (value : α→ℝ) :
    ∃ B : ℝ,0≤B ∧ ∀ c∈cells,value c≤B := by
  induction cells with
  | nil => exact ⟨0,le_rfl,by simp⟩
  | cons c cs ih =>
    obtain ⟨B,hB,hb⟩ := ih
    refine ⟨max (value c) B,hB.trans (le_max_right _ _),?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with rfl|hd
    · exact le_max_left _ _
    · exact (hb d hd).trans (le_max_right _ _)

private theorem finite_uniform_positive {α : Type*} (cells : List α) (value : α→ℝ)
    (hv : ∀ c∈cells,0<value c) : ∃ d : ℝ,0<d ∧ ∀ c∈cells,d≤value c := by
  induction cells with
  | nil => exact ⟨1,by norm_num,by simp⟩
  | cons c cs ih =>
    obtain ⟨d,hd,hb⟩ := ih (fun e he=>hv e (List.mem_cons_of_mem c he))
    refine ⟨min (value c) d,lt_min (hv c List.mem_cons_self) hd,?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl|he
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hb e he)

namespace Transport.ReferenceFluxCell

theorem checked_potential_pointwise {s k : ℕ} (hs : 0<s)
    {start finish flux : ℚ} (cells : List ReferenceFluxCell)
    (hchecks : cells.all (fun c=>c.check s k)=true)
    (hcover : cumulativeIntegralCheck s start finish (cells.map (·.interval))=true)
    (hflux : cells.all (fun c=>decide (c.flux=flux))=true)
    {f : ℝ→ℝ} (hf : IntervalIntegrable f volume (start:ℝ) finish)
    (hp : ∀ c∈cells,∀ᵐ r ∂volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi),
      c.position.Contains s (f r)) :
    ∀ c∈cells,∀ r∈Icc (c.interval.lo:ℝ) c.interval.hi,
      c.potential.Contains s (∫ x in r..(finish:ℝ),f x) ∧
        0<(∫ x in r..(finish:ℝ),f x)-flux-3 := by
  have ho : (start:ℝ)≤finish := by exact_mod_cast cumulativeIntegralCheck_order hcover
  have hlocal (c : ReferenceFluxCell) (hc : c∈cells) :
      IntervalIntegrable f volume (c.interval.lo:ℝ) c.interval.hi := by
    have hb := cumulativeIntegralCheck_cell_bounds hcover (List.mem_map.mpr ⟨c,hc,rfl⟩)
    have hord : (c.interval.lo:ℝ)≤c.interval.hi := by
      exact_mod_cast (cumulativeIntegralCheck_cell_order hcover (List.mem_map.mpr ⟨c,hc,rfl⟩)).le
    apply hf.mono_set
    rw [uIcc_of_le hord,uIcc_of_le ho]
    exact Icc_subset_Icc (by exact_mod_cast hb.1) (by exact_mod_cast hb.2)
  have hsum := cumulativeIntegralCheck_sound hcover (fun d hd=>by
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd
    exact ⟨hlocal c hc,c.checked_position_mass hs (List.all_eq_true.mp hchecks c hc)
      (cumulativeIntegralCheck_cell_order hcover (List.mem_map.mpr ⟨c,hc,rfl⟩)).le
      (hlocal c hc) (hp c hc)⟩)
  intro c hc r hr
  have hh := List.all_eq_true.mp hchecks c hc
  simp only [check,Bool.and_eq_true] at hh
  have hfuture := hsum.2.2 c.interval (List.mem_map.mpr ⟨c,hc,rfl⟩)
  have hpot := IntegerInterval.cumulative_contains hs hh.1.1.1.1.2 hh.1.1.1.2 hr
    (hlocal c hc) hfuture.1 (hp c hc) hfuture.2
  have hpos : 3*(s:ℤ)≤c.weight.lo ∧ (c.flux+3)*(s:ℚ)<(c.potential.lo:ℚ) :=
    of_decide_eq_true hh.1.1.2
  have hfe : c.flux=flux := of_decide_eq_true (List.all_eq_true.mp hflux c hc)
  have hlow : (flux:ℝ)+3<(c.potential.lo:ℝ)/(s:ℝ) := by
    apply (lt_div_iff₀ (by exact_mod_cast hs : (0:ℝ)<s)).mpr
    rw [hfe] at hpos
    exact_mod_cast hpos.2
  exact ⟨hpot,by linarith [IntegerInterval.lower_bound hs hpot]⟩

theorem checked_stieltjes_flux_regular {s k : ℕ} (hs : 0<s)
    {start finish flux : ℚ} (cells : List ReferenceFluxCell) (horder : start<finish)
    (hchecks : cells.all (fun c=>c.check s k)=true)
    (hcover : cumulativeIntegralCheck s start finish (cells.map (·.interval))=true)
    (hflux : cells.all (fun c=>decide (c.flux=flux))=true)
    {f W : ℝ→ℝ} (hf : IntervalIntegrable f volume (start:ℝ) finish)
    (hW : Measurable W)
    (hpw : ∀ c∈cells,∀ r∈Ioo (c.interval.lo:ℝ) c.interval.hi,
      c.position.Contains s (f r) ∧ c.weight.Contains s (W r)) :
    (∀ r∈Icc (start:ℝ) finish,0<(∫ x in r..(finish:ℝ),f x)-flux-3) ∧
    (∃ B : ℝ,∀ᵐ r ∂volume.restrict (Icc (start:ℝ) finish),|W r|≤B) ∧
    IntegrableOn (fun r=>((∫ x in r..(finish:ℝ),f x)-W r-flux)^2/
      ((∫ x in r..(finish:ℝ),f x)-flux-3)) (Icc (start:ℝ) finish) := by
  have hbound (c : ReferenceFluxCell) (hc : c∈cells) :
      ∀ᵐ r ∂volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi),
        c.position.Contains s (f r) ∧ c.weight.Contains s (W r) := by
    rw [←restrict_Ioo_eq_restrict_Icc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with r hr
    exact hpw c hc r hr
  have hpos := fun c hc=>(hbound c hc).mono (fun _ hr=>hr.1)
  have hpot := checked_potential_pointwise hs cells hchecks hcover hflux hf hpos
  obtain ⟨BP,hBP,hbp⟩ := finite_uniform_upper cells (fun c=>(c.potential.maxAbs:ℝ)/(s:ℝ))
  obtain ⟨BW,hBW,hbw⟩ := finite_uniform_upper cells (fun c=>(c.weight.maxAbs:ℝ)/(s:ℝ))
  obtain ⟨delta,hdelta,hd⟩ := finite_uniform_positive cells
    (fun c=>(c.potential.lo:ℝ)/(s:ℝ)-(flux:ℝ)-3) (by
      intro c hc
      have hh := List.all_eq_true.mp hchecks c hc
      simp only [check,Bool.and_eq_true] at hh
      have h : 3*(s:ℤ)≤c.weight.lo ∧ (c.flux+3)*(s:ℚ)<(c.potential.lo:ℚ) := of_decide_eq_true hh.1.1.2
      have he : c.flux=flux := of_decide_eq_true (List.all_eq_true.mp hflux c hc)
      have hl : (flux:ℝ)+3<(c.potential.lo:ℝ)/(s:ℝ) := by
        apply (lt_div_iff₀ (by exact_mod_cast hs : (0:ℝ)<s)).mpr
        rw [he] at h
        exact_mod_cast h.2
      linarith)
  have hglobal : ∀ᵐ r ∂volume.restrict (Icc (start:ℝ) finish),
      |∫ x in r..(finish:ℝ),f x|≤BP ∧ |W r|≤BW ∧
        delta≤(∫ x in r..(finish:ℝ),f x)-flux-3 := by
    apply cumulativeIntegralCheck_ae hcover
    intro d hd'
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd'
    filter_upwards [self_mem_ae_restrict measurableSet_Icc,hbound c hc] with r hr hw
    have hpr := (hpot c hc r hr).1
    exact ⟨(IntegerInterval.abs_bound hs hpr).trans (hbp c hc),
      (IntegerInterval.abs_bound hs hw.2).trans (hbw c hc),
      (hd c hc).trans (by linarith [IntegerInterval.lower_bound hs hpr])⟩
  have ho : (start:ℝ)≤finish := by exact_mod_cast horder.le
  have hP : ContinuousOn (fun r=>∫ x in r..(finish:ℝ),f x) (Icc (start:ℝ) finish) := by
    simpa only [uIcc_of_le ho] using
      intervalIntegral.continuousOn_primitive_interval_left ((intervalIntegrable_iff').mp hf)
  have hPm : AEStronglyMeasurable (fun r=>∫ x in r..(finish:ℝ),f x)
      (volume.restrict (Icc (start:ℝ) finish)) := by
    apply (referenceClamp_comp_continuous ho hP).measurable.aestronglyMeasurable.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with r hr
    simp only [referenceClamp_eq hr]
  refine ⟨?_,⟨BW,hglobal.mono (fun _ h=>h.2.1)⟩,?_⟩
  · intro r hr
    obtain ⟨d,hd',hdr⟩ := cumulativeIntegralCheck_cover horder hcover hr
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd'
    exact (hpot c hc r hdr).2
  · exact Variational.bounded_transport_error_integrable hPm hW.aestronglyMeasurable
      hBP hBW hdelta (hglobal.mono (fun _ h=>h.1))
      (hglobal.mono (fun _ h=>h.2.1)) (hglobal.mono (fun _ h=>h.2.2))

end Transport.ReferenceFluxCell
end OptimalG.Certificates
