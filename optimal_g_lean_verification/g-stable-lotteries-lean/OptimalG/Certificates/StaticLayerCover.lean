import OptimalG.Certificates.StaticLayerPolynomials
import OptimalG.VariationalDomain

/-! A linear-size adjacency checker proves almost-everywhere coverage by the
open interiors of the certified continuous layer cells. Endpoints form a finite
null set; no numerical sampling is used for the coverage conclusion. -/
namespace OptimalG.Certificates.StaticSupport
open Set MeasureTheory

/-- Consecutive, strictly positive-length cells cover the specified interval.
The recursive start parameter also checks every adjacent endpoint equality. -/
def continuousCellCoverCheck (start finish : ℚ) : List ContinuousLayerCell → Bool
  | [] => decide (start = finish)
  | c :: cs => decide (c.lo = start ∧ c.lo < c.hi) && continuousCellCoverCheck c.hi finish cs

theorem continuousCellCoverCheck_interior {start finish : ℚ}
    {cells : List ContinuousLayerCell}
    (hc : continuousCellCoverCheck start finish cells = true)
    {r : ℝ} (hr : r ∈ Ioo (start : ℝ) (finish : ℝ))
    (hne : ∀ c ∈ cells, r ≠ (c.hi : ℝ)) :
    ∃ c ∈ cells, r ∈ Ioo (c.lo : ℝ) (c.hi : ℝ) := by
  induction cells generalizing start with
  | nil =>
      have hh : start = finish := of_decide_eq_true hc
      rw [hh] at hr
      exact False.elim (lt_asymm hr.1 hr.2)
  | cons c cs ih =>
      have hh := Bool.and_eq_true_iff.mp hc
      have hhead : c.lo = start ∧ c.lo < c.hi := of_decide_eq_true hh.1
      by_cases hri : r < (c.hi : ℝ)
      · refine ⟨c,List.mem_cons_self,?_,hri⟩
        simpa only [hhead.1] using hr.1
      · have hne' := hne c List.mem_cons_self
        have hri' : (c.hi : ℝ) < r := lt_of_le_of_ne (le_of_not_gt hri) (Ne.symm hne')
        obtain ⟨d,hd,hdr⟩ := ih hh.2 ⟨hri',hr.2⟩ (fun d hd => hne d (List.mem_cons_of_mem c hd))
        exact ⟨d,List.mem_cons_of_mem c hd,hdr⟩

private theorem ae_avoids_cell_ends (cells : List ContinuousLayerCell) :
    ∀ᵐ r : ℝ ∂volume, ∀ c ∈ cells, r ≠ (c.hi : ℝ) := by
  induction cells with
  | nil => exact Filter.Eventually.of_forall (by simp)
  | cons c cs ih =>
      have hc : ∀ᵐ r : ℝ ∂volume, r ≠ (c.hi : ℝ) := by simp [ae_iff,measure_singleton]
      filter_upwards [hc,ih] with r hrc hrs
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hrc
      · exact hrs d hd

/-- Apart from a null set, every point of the closed target interval lies in
the open interior of some checked cell. -/
theorem continuousCellCoverCheck_ae {start finish : ℚ}
    {cells : List ContinuousLayerCell}
    (hc : continuousCellCoverCheck start finish cells = true) :
    ∀ᵐ r : ℝ ∂volume, r ∈ Icc (start : ℝ) (finish : ℝ) →
      ∃ c ∈ cells, r ∈ Ioo (c.lo : ℝ) (c.hi : ℝ) := by
  have hs : ∀ᵐ r : ℝ ∂volume, r ≠ (start : ℝ) := by simp [ae_iff,measure_singleton]
  have hf : ∀ᵐ r : ℝ ∂volume, r ≠ (finish : ℝ) := by simp [ae_iff,measure_singleton]
  filter_upwards [hs,hf,ae_avoids_cell_ends cells] with r hrs hrf hre
  intro hr
  exact continuousCellCoverCheck_interior hc
    ⟨lt_of_le_of_ne hr.1 (Ne.symm hrs),lt_of_le_of_ne hr.2 hrf⟩ hre

theorem cell_interior_parameter {c : ContinuousLayerCell} {r : ℝ}
    (hr : r ∈ Ioo (c.lo : ℝ) (c.hi : ℝ)) :
    ∃ t ∈ Ioo (0 : ℝ) 1, r = (c.lo : ℝ) + ((c.hi : ℝ)-c.lo)*t := by
  have hd : 0 < (c.hi : ℝ)-(c.lo : ℝ) := sub_pos.mpr (hr.1.trans hr.2)
  refine ⟨(r-c.lo)/(c.hi-c.lo),⟨div_pos (sub_pos.mpr hr.1) hd,?_⟩,?_⟩
  · apply (div_lt_one hd).mpr
    linarith [hr.2]
  · field_simp
    ring

/-- The checked cells cover almost every control's first coordinate, with the
strict interior parameter required by the polynomial support certificates. -/
theorem continuousCellCoverCheck_controls {cells : List ContinuousLayerCell}
    (hc : continuousCellCoverCheck (1/4) (9/25) cells = true) :
    ∀ᵐ q ∂Variational.controlMeasure, ∃ c ∈ cells, ∃ t ∈ Ioo (0 : ℝ) 1,
      q.1 = (c.lo : ℝ) + ((c.hi : ℝ)-c.lo)*t := by
  have hp := continuousCellCoverCheck_ae hc
  have hprod : ∀ᵐ q : Variational.Control ∂volume,
      q.1 ∈ Icc ((1/4 : ℚ) : ℝ) ((9/25 : ℚ) : ℝ) →
        ∃ c ∈ cells, q.1 ∈ Ioo (c.lo : ℝ) (c.hi : ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae hp
  have hm : ∀ᵐ q ∂Variational.controlMeasure, q ∈ Variational.controlDomain :=
    ae_restrict_mem Variational.controlDomain_measurable
  filter_upwards [ae_restrict_of_ae hprod,hm] with q hq hmem
  have hqI : q.1 ∈ Icc ((1/4 : ℚ) : ℝ) ((9/25 : ℚ) : ℝ) := by
    convert! hmem.1 using 1 <;> norm_num [Variational.pLo,Variational.pHi]
  obtain ⟨c,hc,hr⟩ := hq hqI
  obtain ⟨t,ht,he⟩ := cell_interior_parameter hr
  exact ⟨c,hc,t,ht,he⟩

end OptimalG.Certificates.StaticSupport
