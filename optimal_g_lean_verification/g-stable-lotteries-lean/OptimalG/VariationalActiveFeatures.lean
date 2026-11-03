import OptimalG.VariationalFeatureSupport
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Compact active control features, before any continuity of the low score. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

abbrev ContinuationTime := Icc zStart zEnd

noncomputable def featureTrajectorySlack {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (w : ContinuationTime × ControlFeature) : ℝ :=
  featureH hd w.1 (continuation lam d w.1) w.2 -
    vectorField lam d w.1 (continuation lam d w.1)

noncomputable def activeFeatureSet {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    Set (ContinuationTime × ControlFeature) :=
  (univ ×ˢ controlFeatureSupport d) ∩ {w | featureTrajectorySlack hd w = 0}

noncomputable def activeScoreSet {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) : Set (ℝ × ℝ) :=
  (fun w : ContinuationTime × ControlFeature => (w.2.1.2.1,w.2.2.1)) '' activeFeatureSet hd ∪
  (fun w : ContinuationTime × ControlFeature => (w.2.1.2.2,w.2.2.2)) '' activeFeatureSet hd

theorem featureTrajectorySlack_continuous {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    Continuous (featureTrajectorySlack hd) := by
  have hY : Continuous (fun z : ContinuationTime => continuation lam d z) :=
    continuousOn_iff_continuous_restrict.mp (continuation_continuous hd.isContinuation)
  have ht : Continuous (fun w : ContinuationTime × ControlFeature => ((w.1:ℝ),continuation lam d w.1)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (hY.comp continuous_fst)
  exact ((featureH_continuous hd).comp (ht.prodMk continuous_snd)).sub
    (hd.vectorField_continuous.comp ht)

theorem featureTrajectorySlack_nonneg {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    {w : ContinuationTime × ControlFeature} (hw : w.2 ∈ controlFeatureSupport d) :
    0 ≤ featureTrajectorySlack hd w := by
  have hh := (min_le_right (lam-(w.1:ℝ)) _).trans
    (hd.essInf_le_featureH w.1 (continuation lam d w.1) hw)
  exact sub_nonneg.mpr hh

theorem activeFeatureSet_compact {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    IsCompact (activeFeatureSet hd) :=
  (isCompact_univ.prod hd.controlFeatureSupport_compact).inter_right
    (isClosed_eq (featureTrajectorySlack_continuous hd) continuous_const)

theorem activeScoreSet_compact {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    IsCompact (activeScoreSet hd) :=
  ((activeFeatureSet_compact hd).image (by fun_prop)).union
    ((activeFeatureSet_compact hd).image (by fun_prop))

noncomputable def activeScoreGap {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) (v : ℝ × ℝ) : ℝ :=
  by
    classical
    exact if (activeScoreSet hd).Nonempty then Metric.infDist v (activeScoreSet hd) else 1

theorem activeScoreGap_continuous {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    Continuous (activeScoreGap hd) := by
  unfold activeScoreGap
  split_ifs
  · exact Metric.continuous_infDist_pt (s := activeScoreSet hd)
  · exact continuous_const

theorem activeScoreGap_nonneg {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) (v : ℝ × ℝ) :
    0 ≤ activeScoreGap hd v := by
  unfold activeScoreGap
  split_ifs
  · exact Metric.infDist_nonneg
  · norm_num

theorem activeScoreGap_eq_zero_iff {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) (v : ℝ × ℝ) :
    activeScoreGap hd v = 0 ↔ v ∈ activeScoreSet hd := by
  unfold activeScoreGap
  by_cases hne : (activeScoreSet hd).Nonempty
  · rw [if_pos hne]
    exact ((activeScoreSet_compact hd).isClosed.mem_iff_infDist_zero hne).symm
  · rw [if_neg hne]
    have he : activeScoreSet hd = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp [he]

/-- Compactness turns separation from all active rank/score pairs into a uniform
positive control slack, simultaneously for every continuation time. -/
theorem activeScoreGap_control_margin {lam ε : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hε : 0 < ε) :
    ∃ δ > 0, ∀ w : ContinuationTime × ControlFeature, w.2 ∈ controlFeatureSupport d →
      (ε ≤ activeScoreGap hd (w.2.1.2.1,w.2.2.1) ∨ ε ≤ activeScoreGap hd (w.2.1.2.2,w.2.2.2)) →
      δ ≤ featureTrajectorySlack hd w := by
  let K : Set (ContinuationTime × ControlFeature) := (univ ×ˢ controlFeatureSupport d) ∩
    {w | ε ≤ activeScoreGap hd (w.2.1.2.1,w.2.2.1) ∨ ε ≤ activeScoreGap hd (w.2.1.2.2,w.2.2.2)}
  have hK : IsCompact K := by
    apply (isCompact_univ.prod hd.controlFeatureSupport_compact).inter_right
    apply IsClosed.union
    · exact isClosed_le continuous_const ((activeScoreGap_continuous hd).comp (by fun_prop))
    · exact isClosed_le continuous_const ((activeScoreGap_continuous hd).comp (by fun_prop))
  have hpos {w : ContinuationTime × ControlFeature} (hw : w ∈ K) :
      0 < featureTrajectorySlack hd w := by
    apply lt_of_le_of_ne (featureTrajectorySlack_nonneg hd hw.1.2)
    intro he
    have ha : w ∈ activeFeatureSet hd := ⟨hw.1,he.symm⟩
    have hx : (w.2.1.2.1,w.2.2.1) ∈ activeScoreSet hd := Or.inl ⟨w,ha,rfl⟩
    have hy : (w.2.1.2.2,w.2.2.2) ∈ activeScoreSet hd := Or.inr ⟨w,ha,rfl⟩
    have hx0 := (activeScoreGap_eq_zero_iff hd _).mpr hx
    have hy0 := (activeScoreGap_eq_zero_iff hd _).mpr hy
    rcases hw.2 with h | h <;> linarith
  by_cases hne : K.Nonempty
  · obtain ⟨w,hw,hmin⟩ := hK.exists_isMinOn hne (featureTrajectorySlack_continuous hd).continuousOn
    exact ⟨_,hpos hw,fun v hv hg => hmin ⟨⟨mem_univ _,hv⟩,hg⟩⟩
  · refine ⟨1,by norm_num,?_⟩
    intro w hw hg
    exact (hne ⟨w,⟨⟨mem_univ _,hw⟩,hg⟩⟩).elim

end OptimalG.Variational
