import OptimalG.VariationalRegularity
import OptimalG.VariationalIntervalSupport

/-! A certified lower bound for the supporting slope propagates to every
rank of the recovered minimizing score, including the contact endpoint. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

 theorem minimizer_ae_uniform_right_slope {lam c theta : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Icc ell tEnd)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c)
    (htheta : theta ≤ 1)
    (hactiveSlope : ∀ z ∈ Icc zStart zEnd, ∀ v ∈ controlFeatureSupport d,
      featureH hd z (continuation lam d z) v = vectorField lam d z (continuation lam d z) →
      theta ≤ featureTheta lam d v) :
    ∀ᵐ r ∂volume.restrict (Icc ell tEnd), c < r →
      ∀ w ∈ rankScoreSupport d.phi, r ≤ w.1 → w.2+theta*w.1 ≤ d.phi r+theta*r := by
  filter_upwards [minimizer_active_rank_attained hd hl hmin hpass hc hlast] with r hr
  intro hcr w hw hrw
  by_cases hsat : d.phi r = lam-r
  · have hceil := (hd.rankScoreSupport_bounds hw).2.2
    have hh := mul_nonneg (sub_nonneg.mpr htheta) (sub_nonneg.mpr hrw)
    rw [hsat]
    nlinarith only [hceil,hh]
  · obtain ⟨z,hz,v,hv,hactive,hmatch⟩ := hr hcr hsat
    have hlo : quadratic lam z-quadratic lam 1 ≤ continuation lam d z := by
      linarith [hd.continuation_above_root_budget hd.isContinuation hpass hz]
    have hhi := hd.continuation_le_quadratic hd.isContinuation z hz
    have hsupport : w.2+featureTheta lam d v*w.1 ≤ d.phi r+featureTheta lam d v*r := by
      rcases hmatch with hx | hy
      · have hh := active_feature_supports_x hd hz hlo hhi hv hactive hw
        simpa only [hx.1,hx.2] using hh
      · have hdom := (hd.controlFeatureSupport_subset hv).1
        have hp : v.1.1 ≤ w.1 := by
          have hh := (le_max_right _ _).trans hdom.2.2.1
          rw [hy.1] at hh
          exact hh.trans hrw
        have hh := active_feature_supports_y hd hz hlo hhi hv hactive hw hp
        simpa only [hy.1,hy.2] using hh
    have hgap := mul_nonneg (sub_nonneg.mpr (hactiveSlope z hz v hv hactive)) (sub_nonneg.mpr hrw)
    nlinarith only [hsupport,hgap]

 theorem minimizer_uniform_right_slope {lam c theta : ℝ} {d : LowRankData} {psi : ℝ → ℝ}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Ico xLo xHi)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c)
    (hpsi : Continuous psi) (heq : d.phi =ᵐ[volume.restrict (Icc c xHi)] psi)
    (htheta : theta ≤ 1)
    (hactiveSlope : ∀ z ∈ Icc zStart zEnd, ∀ v ∈ controlFeatureSupport d,
      featureH hd z (continuation lam d z) v = vectorField lam d z (continuation lam d z) →
      theta ≤ featureTheta lam d v) :
    ∀ r ∈ Icc c xHi, ∀ s ∈ Icc c xHi, r ≤ s → psi s-psi r ≤ -theta*(s-r) := by
  have hce : ell ≤ c := (by norm_num [ell,xLo] : ell ≤ xLo).trans hc.1
  have hct : c ≤ tEnd := hc.2.le.trans (by norm_num [xHi,tEnd])
  have hright := minimizer_ae_uniform_right_slope hd hl hmin hpass ⟨hce,hct⟩ hlast htheta hactiveSlope
  have heq' : d.phi =ᵐ[volume.restrict (Ioo c xHi)] psi :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self heq
  have hgraph : ∀ s ∈ Icc c xHi, (s,psi s) ∈ rankScoreSupport d.phi :=
    fun s hs => hd.continuous_rep_score_mem hc.2 hc.1 le_rfl hpsi heq' hs
  intro r hr s hs hrs
  by_cases hsc : s = c
  · have hrc : r = c := by linarith [hr.1]
    simp [hsc,hrc]
  · have hcs : c < s := lt_of_le_of_ne hs.1 (Ne.symm hsc)
    have hclosed : IsClosed {t : ℝ | psi s+theta*s ≤ psi t+theta*t} :=
      isClosed_le continuous_const (hpsi.add (continuous_const.mul continuous_id))
    have hsub : Ioo c s ⊆ Icc ell tEnd := by
      intro t ht
      exact ⟨hce.trans ht.1.le,ht.2.le.trans (hs.2.trans (by norm_num [xHi,tEnd]))⟩
    have heqsub : Ioo c s ⊆ Icc c xHi := by
      intro t ht
      exact ⟨ht.1.le,ht.2.le.trans hs.2⟩
    have hh : psi s+theta*s ≤ psi r+theta*r := by
      apply (volume.restrict (Ioo c s)).support_subset_of_isClosed hclosed _
        (mem_support_open_interval_of_closed hcs ⟨hr.1,hrs⟩)
      filter_upwards [ae_restrict_mem measurableSet_Ioo,
        ae_restrict_of_ae_restrict_of_subset hsub hright,
        ae_restrict_of_ae_restrict_of_subset heqsub heq] with t ht hrt het
      have hh := hrt ht.1 (s,psi s) (hgraph s hs) ht.2.le
      simpa only [het] using hh
    nlinarith only [hh]

end OptimalG.Variational
