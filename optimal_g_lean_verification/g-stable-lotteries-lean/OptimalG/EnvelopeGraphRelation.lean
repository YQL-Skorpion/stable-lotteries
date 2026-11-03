import OptimalG.VariationalFeatureReplacement
import OptimalG.VariationalPositiveScores
import Mathlib.Topology.Order.ProjIcc

/-! The running-envelope derivative is either zero or the original score.
Continuity of the original score transfers this relation to the entire compact
essential graph, so replacement ranks may be selected without null-set issues. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem Admissible.rankScore_zero_or_original {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {phi : ℝ → ℝ}
    (hphi : ContinuousOn phi (Icc xLo xHi))
    (hselect : ∀ᵐ r ∂volume.restrict (Icc ell xHi), d.phi r = 0 ∨ d.phi r = phi r)
    {w : ℝ × ℝ} (hw : w ∈ rankScoreSupport d.phi) : w.2 = 0 ∨ w.2 = phi w.1 := by
  let psi : ℝ → ℝ := IccExtend (show xLo ≤ xHi by norm_num [xLo,xHi])
    (fun r : Icc xLo xHi => phi r)
  have hpsi : Continuous psi := (continuousOn_iff_continuous_restrict.mp hphi).Icc_extend'
  have heq (r : ℝ) (hr : r ∈ Icc xLo xHi) : psi r = phi r := IccExtend_of_mem _ _ hr
  have hclosed : IsClosed {w : ℝ × ℝ | w.2 = 0 ∨ w.2 = psi w.1} :=
    (isClosed_eq continuous_snd continuous_const).union (isClosed_eq continuous_snd (hpsi.comp continuous_fst))
  have hmem : w.2 = 0 ∨ w.2 = psi w.1 := by
    apply (rankScoreMeasure d.phi).support_subset_of_isClosed hclosed _ hw
    apply (ae_map_iff hd.rankScoreMap_aemeasurable hclosed.measurableSet).mpr
    have hsub : Icc xLo xHi ⊆ Icc ell xHi :=
      Icc_subset_Icc (by norm_num [ell,xLo]) le_rfl
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae_restrict_of_subset hsub hselect]
      with r hr hs
    change d.phi r = 0 ∨ d.phi r = psi r
    rwa [heq r hr]
  rwa [heq w.1 (hd.rankScoreSupport_bounds hw).1] at hmem

theorem Admissible.exists_common_high_score {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {phi : ℝ → ℝ}
    (hphi : ContinuousOn phi (Icc xLo xHi))
    (hselect : ∀ᵐ r ∂volume.restrict (Icc ell xHi), d.phi r = 0 ∨ d.phi r = phi r) :
    ∃ w ∈ rankScoreSupport d.phi, w.1 ∈ Icc pHi xHi ∧ (9:ℝ)/100 < w.2 ∧ w.2 = phi w.1 := by
  obtain ⟨w,hw,hr,hs⟩ := hd.exists_high_rank_score
  have he := hd.rankScore_zero_or_original hphi hselect hw
  refine ⟨w,hw,hr,hs,?_⟩
  exact he.resolve_left (by intro hz; rw [hz] at hs; norm_num at hs)

theorem zero_score_high_rank_margin {r s theta A : ℝ}
    (hr : r ∈ Icc xLo xHi) (hs : s ∈ Icc pHi xHi)
    (ht : theta ∈ Icc (0:ℝ) 1) (hA : (9:ℝ)/100 < A) : 0 < A+theta*(s-r) := by
  have hr1 := hr.2
  have hs0 := hs.1
  norm_num [xHi,pHi] at hr1 hs0
  have hd : -(2:ℝ)/100 ≤ s-r := by linarith
  have hm := mul_le_mul_of_nonneg_left hd ht.1
  have hn := mul_le_mul_of_nonpos_left ht.2 (by norm_num : -(2:ℝ)/100 ≤ 0)
  nlinarith

/-- Replace zero coordinates by a common positive rank, leaving nonzero
coordinates untouched. Both chosen score values are values of the original
continuous function, and the high-rank control can only decrease. -/
theorem select_original_envelope_feature {lam z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {phi : ℝ → ℝ}
    (hphi : ContinuousOn phi (Icc xLo xHi))
    (hselect : ∀ᵐ r ∂volume.restrict (Icc ell xHi), d.phi r = 0 ∨ d.phi r = phi r)
    (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d) :
    ∃ w ∈ controlFeatureSupport d, w.1.1 = v.1.1 ∧
      w.2.1 = phi w.1.2.1 ∧ w.2.2 = phi w.1.2.2 ∧ featureH hd z u w ≤ featureH hd z u v := by
  obtain ⟨q,hq,hqr,hqs,hqphi⟩ := hd.exists_common_high_score hphi hselect
  have hdom := (hd.controlFeatureSupport_subset hv).1
  have hgraphs := hd.featureSupport_rankScores hv
  have hx := hd.rankScoreSupport_bounds hgraphs.1
  have hy := hd.rankScoreSupport_bounds hgraphs.2
  have hqbound := hd.rankScoreSupport_bounds hq
  have hpq : v.1.1 ≤ q.1 := hdom.1.2.trans hqr.1
  have hxselect : ∃ wx ∈ rankScoreSupport d.phi, wx.2 = phi wx.1 ∧
      featureH hd z u ((v.1.1,wx.1,v.1.2.2),wx.2,v.2.2) ≤ featureH hd z u v := by
    by_cases hx0 : v.2.1 = 0
    · have ht := hd.featureTheta_bounds hv
      have hm := zero_score_high_rank_margin hx.1 hqr ⟨ht.1,ht.2.le⟩ hqs
      have hs : v.2.1+featureTheta lam d v*v.1.2.1 ≤ q.2+featureTheta lam d v*q.1 := by
        rw [hx0] at hm ⊢
        nlinarith only [hm]
      exact ⟨q,hq,hqphi,(hd.feature_x_replacement hdom hz huLow huHigh hqbound.1 hs).1⟩
    · exact ⟨(v.1.2.1,v.2.1),hgraphs.1,(hd.rankScore_zero_or_original hphi hselect hgraphs.1).resolve_left hx0,le_rfl⟩
  obtain ⟨wx,hwx,hwxphi,hxle⟩ := hxselect
  have hwxb := hd.rankScoreSupport_bounds hwx
  have hv' : ((v.1.1,wx.1,v.1.2.2),wx.2,v.2.2) ∈ controlFeatureSupport d :=
    hd.feature_mem_support_of_rankScores hdom.1 hwx hgraphs.2 ((le_max_right _ _).trans hdom.2.2.1)
  have hdom' : (v.1.1,wx.1,v.1.2.2) ∈ controlDomain := ⟨hdom.1,hwxb.1,hdom.2.2⟩
  by_cases hy0 : v.2.2 = 0
  · have ht := hd.featureTheta_bounds hv'
    have hm := zero_score_high_rank_margin hy.1 hqr ⟨ht.1,ht.2.le⟩ hqs
    have hs : v.2.2+featureTheta lam d ((v.1.1,wx.1,v.1.2.2),wx.2,v.2.2)*v.1.2.2 ≤
        q.2+featureTheta lam d ((v.1.1,wx.1,v.1.2.2),wx.2,v.2.2)*q.1 := by
      rw [hy0]
      rw [hy0] at hm
      nlinarith only [hm]
    have hyle := (hd.feature_y_replacement hdom' hz huLow huHigh hqbound.1 hpq hs).1
    exact ⟨((v.1.1,wx.1,q.1),wx.2,q.2),hd.feature_mem_support_of_rankScores hdom.1 hwx hq hpq,
      rfl,hwxphi,hqphi,hyle.trans hxle⟩
  · exact ⟨((v.1.1,wx.1,v.1.2.2),wx.2,v.2.2),hv',rfl,hwxphi,
      (hd.rankScore_zero_or_original hphi hselect hgraphs.2).resolve_left hy0,hxle⟩

end OptimalG.Variational
