import OptimalG.VariationalRankMatching
import OptimalG.VariationalFeatureBounds
import OptimalG.VariationalReferencePullback

/-! The matched score values lie in the original score-graph support almost
everywhere. This supplies the one-dimensional boundary controls before the
competing score has any continuous representative. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped NNReal

 theorem matched_rankScore_support_ae {lam a b m0 : ℝ} {d : LowRankData}
    {J Xi G : ℝ → ℝ} {M : ℝ≥0}
    (hd : Admissible lam d) (hm0 : 0 < m0)
    (hrange : Icc a b ⊆ Icc xLo xHi)
    (hJmono : MonotoneOn J (Icc a b)) (hJlip : LipschitzOnWith M J (Icc a b))
    (hXi : StrictMonoOn Xi (Icc a b))
    (hgrowth : ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, r ≤ s → m0*(s-r) ≤ Xi s-Xi r)
    (hmatch : ∀ r ∈ Icc a b, G r ∈ Icc a b ∧ J (G r)=Xi r) :
    ∀ᵐ r ∂volume.restrict (Icc a b), (G r,d.phi (G r)) ∈ rankScoreSupport d.phi := by
  have hstrict := primitive_matching_strictMono hJmono hXi hmatch
  have hgrow := primitive_matching_growth hJmono hJlip hXi hgrowth hmatch
  let K : ℝ≥0 := ⟨(M:ℝ)/m0,div_nonneg M.coe_nonneg hm0.le⟩
  have hinverse : ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, dist r s ≤ (K:ℝ)*dist (G r) (G s) :=
    primitive_matching_inverse_bound hm0 hstrict.monotoneOn hgrow
  have hp : ∀ᵐ s ∂volume, s ∈ Icc xLo xHi → (s,d.phi s) ∈ rankScoreSupport d.phi :=
    by
      filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp hd.ae_low_rankScore_mem] with s hs hsi
      exact hs ⟨(by norm_num [ell,xLo] : ell ≤ xLo).trans hsi.1,
        hsi.2.trans (by norm_num [xHi,tEnd])⟩ hsi
  filter_upwards [ae_pullback_of_inverse_lipschitz measurableSet_Icc hstrict.injOn hinverse hp,
    ae_restrict_mem measurableSet_Icc] with r hr hri
  exact hr (hrange (hmatch r hri).1)

 theorem matched_late_feature_mem_support {lam a b r s : ℝ} {d : LowRankData} {G : ℝ → ℝ}
    (hd : Admissible lam d) (ha : xLo ≤ a) (hb : b ≤ pHi)
    (hGr : G r ∈ Icc a b) (hGs : G s ∈ Icc a b)
    (hr : (G r,d.phi (G r)) ∈ rankScoreSupport d.phi)
    (hs : (G s,d.phi (G s)) ∈ rankScoreSupport d.phi) :
    ((G r,G s,G r),d.phi (G s),d.phi (G r)) ∈ controlFeatureSupport d := by
  have hp : G r ∈ Icc pLo pHi :=
    ⟨((by norm_num [pLo,xLo] : pLo ≤ xLo).trans ha).trans hGr.1,hGr.2.trans hb⟩
  exact hd.feature_mem_support_of_rankScores hp hs hr le_rfl

 theorem matched_early_feature_mem_support {lam a b p s : ℝ} {d : LowRankData} {G : ℝ → ℝ}
    (hd : Admissible lam d) (hp : p ∈ Icc pLo pHi) (hpa : p ≤ a)
    (hGs : G s ∈ Icc a b) (hs : (G s,d.phi (G s)) ∈ rankScoreSupport d.phi) :
    ((p,G s,G s),d.phi (G s),d.phi (G s)) ∈ controlFeatureSupport d :=
  hd.feature_mem_support_of_rankScores hp hs hs (hpa.trans hGs.1)

end OptimalG.Variational
