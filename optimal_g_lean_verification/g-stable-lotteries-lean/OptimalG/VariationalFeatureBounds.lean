import OptimalG.VariationalFeatureGeometry

/-! Bounds and algebra on the complete essential rank/score support. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

private theorem testInterval_subset_lowInterval : Icc xLo xHi ⊆ Icc ell tEnd :=
  Icc_subset_Icc (by norm_num [ell,xLo]) (by norm_num [xHi,tEnd])

theorem Admissible.rankScoreMap_aemeasurable {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    AEMeasurable (rankScoreMap d.phi) (volume.restrict (Icc xLo xHi)) :=
  measurable_id.aemeasurable.prodMk
    (AEStronglyMeasurable.mono_set testInterval_subset_lowInterval hd.2.2.1.aestronglyMeasurable).aemeasurable

theorem Admissible.ae_low_rankScore_mem {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    ∀ᵐ r ∂volume.restrict (Icc ell tEnd), r ∈ Icc xLo xHi → (r,d.phi r) ∈ rankScoreSupport d.phi := by
  have hh : ∀ᵐ r ∂volume.restrict (Icc xLo xHi), (r,d.phi r) ∈ rankScoreSupport d.phi :=
    ae_of_ae_map hd.rankScoreMap_aemeasurable (rankScoreMeasure d.phi).support_mem_ae
  exact ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Icc).mp hh)

theorem Admissible.featureSupport_rankScores {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d) :
    (v.1.2.1,v.2.1) ∈ rankScoreSupport d.phi ∧ (v.1.2.2,v.2.2) ∈ rankScoreSupport d.phi := by
  have hclosed : IsClosed {v : ControlFeature | (v.1.2.1,v.2.1) ∈ rankScoreSupport d.phi ∧
      (v.1.2.2,v.2.2) ∈ rankScoreSupport d.phi} :=
    ((rankScoreMeasure d.phi).isClosed_support.preimage (by fun_prop)).inter
      ((rankScoreMeasure d.phi).isClosed_support.preimage (by fun_prop))
  apply (controlFeatureMeasure d).support_subset_of_isClosed hclosed _ hv
  apply (ae_map_iff hd.controlFeatureMap_aemeasurable hclosed.measurableSet).mpr
  filter_upwards [ae_control_lowRanks _ hd.ae_low_rankScore_mem,ae_restrict_mem controlDomain_measurable] with c hc hdom
  exact ⟨hc.1 hdom.2.1,hc.2 ⟨(le_max_left _ _).trans hdom.2.2.1,hdom.2.2.2⟩⟩

theorem Admissible.rankScoreSupport_bounds {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    {v : ℝ × ℝ} (hv : v ∈ rankScoreSupport d.phi) :
    v.1 ∈ Icc xLo xHi ∧ 0 ≤ v.2 ∧ v.2 ≤ lam-v.1 := by
  have hclosed : IsClosed {v : ℝ × ℝ | v.1 ∈ Icc xLo xHi ∧ 0 ≤ v.2 ∧ v.2 ≤ lam-v.1} :=
    (isClosed_Icc.preimage continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter (isClosed_le continuous_snd (by fun_prop)))
  apply (rankScoreMeasure d.phi).support_subset_of_isClosed hclosed _ hv
  apply (ae_map_iff hd.rankScoreMap_aemeasurable hclosed.measurableSet).mpr
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae_restrict_of_subset testInterval_subset_lowInterval hd.2.2.2.1] with r hr hb
  exact ⟨hr,hb⟩

theorem featureH_eq_value {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (z u A B : ℝ) {c : Control} (hc : c ∈ controlDomain) :
    featureH hd z u (c,A,B) = Certificates.Control.value (z-lam) (2*lam-c.2.1)
      (c.1+c.2.2-lam) (primitive lam d c.1) (quadratic lam (1-c.1)-d.S)
      (quadratic lam (z-c.1)-d.S-u) A B := by
  unfold featureH featureDet
  dsimp only
  rw [controlPrimitiveExtension_eq hd hc.1]
  have hD := (hd.determinant_positive hc).le
  change _ / max (3/100) (controlDeterminant lam d c) = _
  rw [max_eq_right hD]
  rfl

noncomputable def featureTheta (lam : ℝ) (d : LowRankData) (v : ControlFeature) : ℝ :=
  Certificates.Control.theta (2*lam-v.1.2.1) (v.1.1+v.1.2.2-lam)
    (primitive lam d v.1.1) (quadratic lam (1-v.1.1)-d.S) v.2.1 v.2.2

theorem Admissible.featureTheta_bounds {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d) :
    0 ≤ featureTheta lam d v ∧ featureTheta lam d v < 1 := by
  have hc := (hd.controlFeatureSupport_subset hv).1
  have hx := hd.rankScoreSupport_bounds (hd.featureSupport_rankScores hv).1
  have hy := hd.rankScoreSupport_bounds (hd.featureSupport_rankScores hv).2
  have hR := hd.control_R_lower hc.1
  have hP := (hd.control_P_bounds hc.1).1
  have hD : 0 < Certificates.Control.det (2*lam-v.1.2.1) (v.1.1+v.1.2.2-lam)
      (primitive lam d v.1.1) (quadratic lam (1-v.1.1)-d.S) := by
    change 0 < controlDeterminant lam d v.1
    linarith [hd.determinant_positive hc]
  constructor
  · apply div_nonneg _ hD.le
    exact add_nonneg (mul_nonneg (by linarith) hx.2.1) (mul_nonneg hP hy.2.1)
  · unfold featureTheta Certificates.Control.theta
    apply (div_lt_one hD).mpr
    exact Certificates.Control.score_gap lam v.1.1 v.1.2.1 v.1.2.2 _ _ _ _
      (by linarith) hP hx.2.2 hy.2.2 (by linarith [hd.control_binary_gap hc])

end OptimalG.Variational
