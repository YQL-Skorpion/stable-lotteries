import OptimalG.VariationalDefs
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod

/-! # The compact, positive-measure domain of three-class controls -/

namespace OptimalG.Variational

open Set MeasureTheory

theorem controlDomain_eq_box_inter :
    controlDomain =
      (Icc pLo pHi ×ˢ (Icc xLo xHi ×ˢ Icc xLo xHi)) ∩
        {c : Control | c.1 ≤ c.2.2} := by
  ext c
  simp only [controlDomain, mem_setOf_eq, mem_Icc, max_le_iff,
    mem_inter_iff, mem_prod]
  tauto

theorem controlDomain_isClosed : IsClosed controlDomain := by
  rw [controlDomain_eq_box_inter]
  apply IsClosed.inter
  · exact isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc)
  · exact isClosed_le continuous_fst (continuous_snd.comp continuous_snd)

theorem controlDomain_isCompact : IsCompact controlDomain := by
  apply (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset
    controlDomain_isClosed
  rw [controlDomain_eq_box_inter]
  exact inter_subset_left

theorem controlDomain_measurable : MeasurableSet controlDomain :=
  controlDomain_isClosed.measurableSet

theorem controlDomain_volume_pos : 0 < volume controlDomain := by
  let box : Set Control :=
    Ioo (25 / 100 : ℝ) (26 / 100) ×ˢ
      (Ioo (30 / 100 : ℝ) (31 / 100) ×ˢ Ioo (32 / 100 : ℝ) (33 / 100))
  have hopen : IsOpen box := isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)
  have hne : box.Nonempty := by
    refine ⟨((255 : ℝ) / 1000, (305 : ℝ) / 1000, (325 : ℝ) / 1000), ?_⟩
    norm_num [box]
  have hsub : box ⊆ controlDomain := by
    intro c hc
    rcases hc with ⟨hp, hx, hy⟩
    dsimp [controlDomain]
    simp only [mem_Icc, max_le_iff]
    norm_num [pLo, pHi, xLo, xHi] at *
    constructor
    · constructor <;> linarith [hp.1, hp.2]
    constructor
    · constructor <;> linarith [hx.1, hx.2]
    constructor
    · constructor <;> linarith [hy.1, hp.2]
    · linarith [hy.2]
  exact (hopen.measure_pos volume hne).trans_le (measure_mono hsub)

instance controlMeasure_neZero : NeZero controlMeasure := by
  constructor
  intro h
  have hm := congrArg (fun m : Measure Control => m univ) h
  have hzero : volume controlDomain = 0 := by simpa [controlMeasure] using hm
  exact (ne_of_gt controlDomain_volume_pos) hzero

instance controlMeasure_finite : IsFiniteMeasure controlMeasure := by
  unfold controlMeasure
  exact isFiniteMeasure_restrict.mpr controlDomain_isCompact.measure_lt_top.ne

/-- A null exceptional set of low ranks gives null exceptional sets for either
low coordinate of the three-dimensional control domain. -/
theorem ae_control_lowRanks (P : ℝ → Prop)
    (hP : ∀ᵐ r ∂volume.restrict (Icc ell tEnd), P r) :
    ∀ᵐ c ∂controlMeasure, P c.2.1 ∧ P c.2.2 := by
  have hglobal : ∀ᵐ r ∂volume, r ∈ Icc ell tEnd → P r :=
    (ae_restrict_iff' measurableSet_Icc).mp hP
  have hxpair : ∀ᵐ c : ℝ × ℝ ∂volume, c.1 ∈ Icc ell tEnd → P c.1 :=
    Measure.quasiMeasurePreserving_fst.ae hglobal
  have hypair : ∀ᵐ c : ℝ × ℝ ∂volume, c.2 ∈ Icc ell tEnd → P c.2 :=
    Measure.quasiMeasurePreserving_snd.ae hglobal
  have hx : ∀ᵐ c : Control ∂volume, c.2.1 ∈ Icc ell tEnd → P c.2.1 :=
    Measure.quasiMeasurePreserving_snd.ae hxpair
  have hy : ∀ᵐ c : Control ∂volume, c.2.2 ∈ Icc ell tEnd → P c.2.2 :=
    Measure.quasiMeasurePreserving_snd.ae hypair
  change ∀ᵐ c ∂volume.restrict controlDomain, P c.2.1 ∧ P c.2.2
  filter_upwards [ae_restrict_of_ae hx, ae_restrict_of_ae hy,
    ae_restrict_mem controlDomain_measurable] with c hxc hyc hc
  have hcx := hc.2.1
  have hcy := hc.2.2
  constructor
  · apply hxc
    norm_num [ell, tEnd, xLo, xHi] at *
    constructor <;> linarith [hcx.1, hcx.2]
  · apply hyc
    have hyl := (le_max_left xLo c.1).trans hcy.1
    norm_num [ell, tEnd, xLo, xHi] at *
    constructor <;> linarith [hyl, hcy.2]

end OptimalG.Variational
