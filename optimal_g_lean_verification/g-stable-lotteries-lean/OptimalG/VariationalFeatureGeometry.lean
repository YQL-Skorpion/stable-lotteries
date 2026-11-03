import OptimalG.VariationalActiveRanks
import OptimalG.VariationalRankShift

/-! Product geometry of the essential rank/score graph. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

private theorem support_prod_of_mem {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite ν]
    {x : X} {y : Y} (hx : x ∈ μ.support) (hy : y ∈ ν.support) : (x,y) ∈ (μ.prod ν).support := by
  apply (Measure.mem_support_iff_forall _).mpr
  intro U hU
  obtain ⟨s,hs,t,ht,hst⟩ := mem_nhds_prod_iff.mp hU
  have hspos := (Measure.mem_support_iff_forall x).mp hx s hs
  have htpos := (Measure.mem_support_iff_forall y).mp hy t ht
  have hpos : 0 < (μ.prod ν) (s ×ˢ t) := by
    simpa only [Measure.prod_prod] using ENNReal.mul_pos hspos.ne' htpos.ne'
  exact hpos.trans_le (measure_mono hst)

private theorem support_map_of_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace Y] [HereditarilyLindelofSpace Y]
    (μ : Measure X) {f : X → Y} (hf : Continuous f) (hm : AEMeasurable f μ)
    {x : X} (hx : x ∈ μ.support) : f x ∈ (μ.map f).support := by
  exact μ.support_subset_of_isClosed ((μ.map f).isClosed_support.preimage hf)
    (ae_of_ae_map hm (μ.map f).support_mem_ae) hx

private theorem mem_support_volume_Icc {a b r : ℝ} (hab : a < b) (hr : r ∈ Icc a b) :
    r ∈ (volume.restrict (Icc a b)).support := by
  have hsub : Ioo a b ⊆ (volume.restrict (Icc a b)).support := by
    intro s hs
    apply Measure.interior_inter_support
    refine ⟨?_,?_⟩
    · simpa only [interior_Icc] using hs
    · simp only [Measure.support_eq_univ,mem_univ]
  have hh := closure_minimal hsub (volume.restrict (Icc a b)).isClosed_support
  rw [closure_Ioo hab.ne] at hh
  exact hh hr

noncomputable def rankScoreMap (f : ℝ → ℝ) (r : ℝ) : ℝ × ℝ := (r,f r)
noncomputable def rankScoreMeasure (f : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Icc xLo xHi)).map (rankScoreMap f)
instance rankScoreMeasure_finite (f : ℝ → ℝ) : IsFiniteMeasure (rankScoreMeasure f) := by
  unfold rankScoreMeasure
  infer_instance
noncomputable def rankScoreSupport (f : ℝ → ℝ) : Set (ℝ × ℝ) := (rankScoreMeasure f).support
noncomputable def fullControlBox : Set Control := Icc pLo pHi ×ˢ (Icc xLo xHi ×ˢ Icc xLo xHi)
noncomputable def featurePack (w : ℝ × ((ℝ × ℝ) × (ℝ × ℝ))) : ControlFeature :=
  ((w.1,w.2.1.1,w.2.2.1),w.2.1.2,w.2.2.2)
noncomputable def fullFeatureMeasure (f : ℝ → ℝ) : Measure ControlFeature :=
  (volume.restrict fullControlBox).map (fun c => (c,f c.2.1,f c.2.2))
noncomputable def featureCut : Set ControlFeature := {v | v.1.1 ≤ v.1.2.2}

@[fun_prop] theorem featurePack_continuous : Continuous featurePack := by
  unfold featurePack
  fun_prop
@[fun_prop] theorem featurePack_measurable : Measurable featurePack := featurePack_continuous.measurable

theorem rankScoreMap_measurable {f : ℝ → ℝ} (hf : Measurable f) : Measurable (rankScoreMap f) :=
  measurable_id.prodMk hf

theorem fullFeatureMeasure_eq_product {f : ℝ → ℝ} (hf : Measurable f) :
    fullFeatureMeasure f = ((volume.restrict (Icc pLo pHi)).prod
      ((rankScoreMeasure f).prod (rankScoreMeasure f))).map featurePack := by
  have hg := rankScoreMap_measurable hf
  have hbox : (volume.restrict fullControlBox) =
      (volume.restrict (Icc pLo pHi)).prod
        ((volume.restrict (Icc xLo xHi)).prod (volume.restrict (Icc xLo xHi))) := by
    rw [Measure.prod_restrict,Measure.prod_restrict]
    rfl
  rw [fullFeatureMeasure,hbox,rankScoreMeasure,Measure.map_prod_map _ _ hg hg]
  have hh := Measure.map_prod_map (volume.restrict (Icc pLo pHi))
    ((volume.restrict (Icc xLo xHi)).prod (volume.restrict (Icc xLo xHi))) measurable_id (hg.prodMap hg)
  simp only [Measure.map_id] at hh
  rw [hh,Measure.map_map (by fun_prop) (measurable_id.prodMap (hg.prodMap hg))]
  rfl

theorem controlFeatureMeasure_eq_cut {f : ℝ → ℝ} (hf : Measurable f) (S : ℝ) :
    controlFeatureMeasure ⟨S,f⟩ = (fullFeatureMeasure f).restrict featureCut := by
  have hmap : Measurable (fun c : Control => (c,f c.2.1,f c.2.2)) := by fun_prop
  have hcut : MeasurableSet featureCut := (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  rw [fullFeatureMeasure,Measure.restrict_map hmap hcut]
  have heq : (volume.restrict fullControlBox).restrict
      ((fun c : Control => (c,f c.2.1,f c.2.2)) ⁻¹' featureCut) = controlMeasure := by
    rw [Measure.restrict_restrict (hmap hcut)]
    unfold controlMeasure
    congr 1
    rw [controlDomain_eq_box_inter]
    ext c
    simp [fullControlBox,featureCut,and_comm]
  rw [heq]
  rfl

/-- Every pair of essential rank/score graph points supplies an admissible
support control when the second rank is strictly above the mass. -/
theorem feature_mem_support_of_rankScores_strict {f : ℝ → ℝ} (hf : Measurable f) (S : ℝ)
    {p : ℝ} {v w : ℝ × ℝ} (hp : p ∈ Icc pLo pHi)
    (hv : v ∈ rankScoreSupport f) (hw : w ∈ rankScoreSupport f) (hpy : p < w.1) :
    ((p,v.1,w.1),v.2,w.2) ∈ controlFeatureSupport ⟨S,f⟩ := by
  have hprod := support_prod_of_mem (volume.restrict (Icc pLo pHi)) _
    (mem_support_volume_Icc (by norm_num [pLo,pHi]) hp)
    (support_prod_of_mem (rankScoreMeasure f) (rankScoreMeasure f) hv hw)
  have hfull := support_map_of_continuous _ (f := featurePack) (by fun_prop) (by fun_prop) hprod
  rw [← fullFeatureMeasure_eq_product hf] at hfull
  change _ ∈ (controlFeatureMeasure ⟨S,f⟩).support
  rw [controlFeatureMeasure_eq_cut hf S]
  apply Measure.interior_inter_support
  refine ⟨?_,hfull⟩
  have hopen : IsOpen {v : ControlFeature | v.1.1 < v.1.2.2} := isOpen_lt (by fun_prop) (by fun_prop)
  have hsub : {v : ControlFeature | v.1.1 < v.1.2.2} ⊆ featureCut := by
    intro v hv
    change v.1.1 < v.1.2.2 at hv
    exact hv.le
  exact mem_interior.mpr ⟨_,hsub,hopen,hpy⟩

theorem rankScoreSupport_rank {f : ℝ → ℝ} (hf : Measurable f)
    {v : ℝ × ℝ} (hv : v ∈ rankScoreSupport f) : v.1 ∈ Icc xLo xHi := by
  apply (rankScoreMeasure f).support_subset_of_isClosed
    (isClosed_Icc.preimage continuous_fst) _ hv
  apply (ae_map_iff (rankScoreMap_measurable hf).aemeasurable
    (measurableSet_Icc.preimage measurable_fst)).mpr
  exact ae_restrict_mem measurableSet_Icc

/-- The boundary y=p is reached by approaching from smaller admissible masses. -/
theorem feature_mem_support_of_rankScores {f : ℝ → ℝ} (hf : Measurable f) (S : ℝ)
    {p : ℝ} {v w : ℝ × ℝ} (hp : p ∈ Icc pLo pHi)
    (hv : v ∈ rankScoreSupport f) (hw : w ∈ rankScoreSupport f) (hpy : p ≤ w.1) :
    ((p,v.1,w.1),v.2,w.2) ∈ controlFeatureSupport ⟨S,f⟩ := by
  rcases lt_or_eq_of_le hpy with hlt | heq
  · exact feature_mem_support_of_rankScores_strict hf S hp hv hw hlt
  · have hlow := (rankScoreSupport_rank hf hw).1
    have hplo : pLo < p := by rw [heq]; exact (by norm_num [pLo,xLo] : pLo < xLo).trans_le hlow
    obtain ⟨pn,_,hpn,ht⟩ := exists_seq_strictMono_tendsto' hplo
    apply (controlFeatureMeasure ⟨S,f⟩).isClosed_support.mem_of_tendsto
      ((ht.prodMk_nhds tendsto_const_nhds).prodMk_nhds tendsto_const_nhds)
    exact Eventually.of_forall fun n => feature_mem_support_of_rankScores_strict hf S
      ⟨(hpn n).1.le,(hpn n).2.le.trans hp.2⟩ hv hw ((hpn n).2.trans_le hpy)

noncomputable def admissibleScoreRep {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) : ℝ → ℝ :=
  hd.2.2.1.aestronglyMeasurable.mk d.phi

theorem admissibleScoreRep_measurable {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    Measurable (admissibleScoreRep hd) := hd.2.2.1.aestronglyMeasurable.measurable_mk

theorem admissibleScoreRep_ae_eq {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    d.phi =ᵐ[volume.restrict (Icc ell tEnd)] admissibleScoreRep hd :=
  hd.2.2.1.aestronglyMeasurable.ae_eq_mk

theorem controlFeatureMeasure_congr {d e : LowRankData}
    (heq : d.phi =ᵐ[volume.restrict (Icc ell tEnd)] e.phi) :
    controlFeatureMeasure d = controlFeatureMeasure e := by
  apply Measure.map_congr
  filter_upwards [ae_control_lowRanks (fun r => d.phi r=e.phi r) heq] with c hc
  simp only [controlFeatureMap,hc.1,hc.2]

theorem rankScoreMeasure_congr {f g : ℝ → ℝ}
    (heq : f =ᵐ[volume.restrict (Icc ell tEnd)] g) : rankScoreMeasure f = rankScoreMeasure g := by
  apply Measure.map_congr
  have hsub : Icc xLo xHi ⊆ Icc ell tEnd := Icc_subset_Icc
    (by norm_num [ell,xLo]) (by norm_num [xHi,tEnd])
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub heq] with r hr
  simp only [rankScoreMap,hr]

/-- The full geometric support characterization holds for an arbitrary
admissible measurable score, using a Borel representative only in the proof. -/
theorem Admissible.feature_mem_support_of_rankScores {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {p : ℝ} {v w : ℝ × ℝ} (hp : p ∈ Icc pLo pHi)
    (hv : v ∈ rankScoreSupport d.phi) (hw : w ∈ rankScoreSupport d.phi) (hpy : p ≤ w.1) :
    ((p,v.1,w.1),v.2,w.2) ∈ controlFeatureSupport d := by
  have hmeasure := controlFeatureMeasure_congr (d := d) (e := ⟨d.S,admissibleScoreRep hd⟩)
    (admissibleScoreRep_ae_eq hd)
  have hrank := rankScoreMeasure_congr (admissibleScoreRep_ae_eq hd)
  unfold controlFeatureSupport
  rw [hmeasure]
  apply OptimalG.Variational.feature_mem_support_of_rankScores (admissibleScoreRep_measurable hd) d.S hp _ _ hpy
  · change v ∈ (rankScoreMeasure (admissibleScoreRep hd)).support
    rwa [← hrank]
  · change w ∈ (rankScoreMeasure (admissibleScoreRep hd)).support
    rwa [← hrank]

end OptimalG.Variational
