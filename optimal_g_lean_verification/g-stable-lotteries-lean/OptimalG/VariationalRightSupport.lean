import OptimalG.VariationalSupportingFeatures

/-! Right supporting lines at almost every rank of a minimizing measurable score. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

theorem minimizer_right_support {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Icc ell tEnd)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c) :
    ∀ᵐ r ∂volume.restrict (Icc ell tEnd), c < r →
      ∃ θ ∈ Icc (0:ℝ) 1, ∀ w ∈ rankScoreSupport d.phi, r ≤ w.1 →
        w.2+θ*w.1 ≤ d.phi r+θ*r := by
  filter_upwards [minimizer_active_rank_attained hd hl hmin hpass hc hlast] with r hr
  intro hcr
  by_cases heq : d.phi r = lam-r
  · refine ⟨1,by norm_num,?_⟩
    intro w hw _
    have hceil := (hd.rankScoreSupport_bounds hw).2.2
    rw [heq]
    nlinarith
  · obtain ⟨z,hz,v,hv,hactive,hmatch⟩ := hr hcr heq
    refine ⟨featureTheta lam d v,⟨(hd.featureTheta_bounds hv).1,(hd.featureTheta_bounds hv).2.le⟩,?_⟩
    intro w hw hrw
    have huLow : quadratic lam z-quadratic lam 1 ≤ continuation lam d z := by
      linarith [hd.continuation_above_root_budget hd.isContinuation hpass hz]
    have huHigh := hd.continuation_le_quadratic hd.isContinuation z hz
    rcases hmatch with hx | hy
    · have hh := active_feature_supports_x hd hz huLow huHigh hv hactive hw
      rwa [hx.1,hx.2] at hh
    · have hdom := (hd.controlFeatureSupport_subset hv).1
      have hpw : v.1.1 ≤ w.1 := by
        have hpy := (le_max_right _ _).trans hdom.2.2.1
        rw [hy.1] at hpy
        exact hpy.trans hrw
      have hh := active_feature_supports_y hd hz huLow huHigh hv hactive hw hpw
      rwa [hy.1,hy.2] at hh

/-- The measurable minimizing score is nonincreasing almost everywhere after
its final cap contact, before a continuous representative has been selected. -/
theorem minimizer_ae_antitone_after_contact {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Icc ell tEnd)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c) :
    ∀ᵐ r ∂volume.restrict (Icc ell tEnd), c < r →
      ∀ w ∈ rankScoreSupport d.phi, r ≤ w.1 → w.2 ≤ d.phi r := by
  filter_upwards [minimizer_right_support hd hl hmin hpass hc hlast] with r hr
  intro hcr w hw hrw
  obtain ⟨θ,hθ,hbound⟩ := hr hcr
  have hh := hbound w hw hrw
  have hmul := mul_le_mul_of_nonneg_left hrw hθ.1
  linarith

end OptimalG.Variational
