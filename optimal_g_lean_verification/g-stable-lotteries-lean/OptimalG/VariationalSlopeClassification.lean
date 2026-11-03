import OptimalG.VariationalActiveDiagonal
import OptimalG.VariationalRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! Actual almost-everywhere slope classification of the minimizing score,
including the coupled diagonal boundary. Numerical slope bounds can now be
applied to these proved alternatives. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

noncomputable def diagonalFeatureSlope (lam : ℝ) (d : LowRankData) (z u : ℝ)
    (v : ControlFeature) (r B : ℝ) : ℝ :=
  Certificates.Control.diagonalSlope (z-lam) (2*lam-v.1.2.1) (2*r-lam)
    (primitive lam d r) (quadratic lam (1-r)-d.S) (quadratic lam (z-r)-d.S-u)
    v.2.1 B (1-r-lam) (z-r-lam)

 theorem active_rank_derivative_cases {lam z u c r slope : ℝ} {d : LowRankData} {psi : ℝ → ℝ}
    (hd : Admissible lam d) (hc : xLo ≤ c) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    (hgraph : ∀ s ∈ Icc c xHi, (s,psi s) ∈ rankScoreSupport d.phi)
    (hr : r ∈ Ioo c xHi) (hne : r ≠ pHi)
    (hder : HasDerivAt psi slope r) (hJ : HasDerivAt (primitive lam d) (psi r) r)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hactive : featureH hd z u v = vectorField lam d z u)
    (hrank : (v.1.2.1 = r ∧ v.2.1 = psi r) ∨ (v.1.2.2 = r ∧ v.2.2 = psi r)) :
    slope = -featureTheta lam d v ∨
      (v.1.1 = r ∧ v.1.2.2 = r ∧ v.1.2.1 ≤ r ∧ r ∈ Ioo pLo pHi ∧
        slope = diagonalFeatureSlope lam d z u v r (psi r)) := by
  rcases hrank with hx | hy
  · exact Or.inl (active_x_derivative hd hz huLow huHigh hgraph hr hder hv hactive hx.1 hx.2)
  · have hdom := (hd.controlFeatureSupport_subset hv).1
    have hp : v.1.1 ≤ r := by
      have hh := (le_max_right xLo v.1.1).trans hdom.2.2.1
      rwa [hy.1] at hh
    rcases hp.eq_or_lt with heq | hlt
    · by_cases hx : r ≤ v.1.2.1
      · exact Or.inl (active_y_boundary_with_right_x_derivative hd hz huLow huHigh hgraph hr hder
          hv hactive hy.1 hy.2 heq hx)
      · have hpr : r ∈ Ioo pLo pHi := by
          constructor
          · have hh : pLo < xLo := by norm_num [pLo,xLo]
            exact (hh.trans_le hc).trans hr.1
          · have hh := hdom.1.2
            rw [heq] at hh
            exact lt_of_le_of_ne hh hne
        refine Or.inr ⟨heq,hy.1,(lt_of_not_ge hx).le,hpr,?_⟩
        exact active_y_diagonal_derivative hd hz huLow huHigh hgraph hr hpr hder hJ hv hactive
          hy.1 hy.2 heq
    · exact Or.inl (active_y_interior_derivative hd hz huLow huHigh hgraph hr hder hv hactive
        hy.1 hy.2 hlt)

 theorem minimizer_slope_classification_strong {lam c : ℝ} {d : LowRankData} {psi : ℝ → ℝ} {L : ℝ≥0}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Ico xLo xHi)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c)
    (hpsi : LipschitzWith L psi) (heq : d.phi =ᵐ[volume.restrict (Icc c xHi)] psi)
    (hprimitive : ∀ r ∈ Icc c xHi, lowPrimitive lam d r = cap lam d.S c+∫ t in c..r, psi t) :
    ∀ᵐ r ∂volume.restrict (Ioo c xHi), HasDerivAt psi (deriv psi r) r ∧
      ((psi r = lam-r ∧ deriv psi r = -1) ∨ ∃ z ∈ Icc zStart zEnd, ∃ v ∈ controlFeatureSupport d,
        featureH hd z (continuation lam d z) v = vectorField lam d z (continuation lam d z) ∧
        (deriv psi r = -featureTheta lam d v ∨
          (v.1.1 = r ∧ v.1.2.2 = r ∧ v.1.2.1 ≤ r ∧ r ∈ Ioo pLo pHi ∧
            deriv psi r = diagonalFeatureSlope lam d z (continuation lam d z) v r (psi r)))) := by
  have hce : ell ≤ c := (by norm_num [ell,xLo] : ell ≤ xLo).trans hc.1
  have hct : c ≤ tEnd := hc.2.le.trans (by norm_num [xHi,tEnd])
  have hsub : Ioo c xHi ⊆ Icc ell tEnd := by
    intro r hr
    exact ⟨hce.trans hr.1.le,hr.2.le.trans (by norm_num [xHi,tEnd])⟩
  have hgraph : ∀ r ∈ Icc c xHi, (r,psi r) ∈ rankScoreSupport d.phi :=
    fun r hr => hd.continuous_rep_score_mem hc.2 hc.1 le_rfl hpsi.continuous
      (by simpa only [restrict_Ioo_eq_restrict_Icc] using heq) hr
  have hAC : AbsolutelyContinuousOnInterval psi c xHi := hpsi.lipschitzOnWith.absolutelyContinuousOnInterval
  have hdiff : ∀ᵐ r ∂volume.restrict (Icc c xHi), DifferentiableAt ℝ psi r := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    simpa only [uIcc_of_le hc.2.le] using hAC.ae_differentiableAt
  have hne : ∀ᵐ r ∂volume, r ≠ pHi := by simp [ae_iff]
  have hactive := minimizer_active_rank_attained hd hl hmin hpass ⟨hce,hct⟩ hlast
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hdiff,
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self heq,
    ae_restrict_of_ae_restrict_of_subset hsub hactive,
    ae_restrict_of_ae hne] with r hr hdr heq hractive hrne
  refine ⟨hdr.hasDerivAt,?_⟩
  by_cases hsat : psi r = lam-r
  · apply Or.inl
    refine ⟨hsat,?_⟩
    exact derivative_eq_line_at_saturation hr hdr.hasDerivAt
      (fun s hs => (hd.rankScoreSupport_bounds (hgraph s hs)).2.2) hsat
  · obtain ⟨z,hz,v,hv,hvactive,hvpos⟩ := hractive hr.1 (by simpa only [heq] using hsat)
    have hJlow := hasDerivAt_lowPrimitive_of_rep hpsi.continuous hr hprimitive
    have hJ : HasDerivAt (primitive lam d) (psi r) r := by
      apply hJlow.congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
      have hte : ell < t := hce.trans_lt ht.1
      have htt : t ≤ tEnd := ht.2.le.trans (by norm_num [xHi,tEnd])
      simp only [primitive,if_neg (not_le.mpr hte),if_pos htt]
    have hlo : quadratic lam z-quadratic lam 1 ≤ continuation lam d z := by
      have hh := hd.continuation_above_root_budget hd.isContinuation hpass hz
      linarith
    have hhi := hd.continuation_le_quadratic hd.isContinuation z hz
    refine Or.inr ⟨z,hz,v,hv,hvactive,?_⟩
    apply active_rank_derivative_cases hd hc.1 hz hlo hhi hgraph hr hrne hdr.hasDerivAt hJ hv hvactive
    simpa only [heq] using hvpos

 theorem minimizer_slope_classification {lam c : ℝ} {d : LowRankData} {psi : ℝ → ℝ} {L : ℝ≥0}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Ico xLo xHi)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c)
    (hpsi : LipschitzWith L psi) (heq : d.phi =ᵐ[volume.restrict (Icc c xHi)] psi)
    (hprimitive : ∀ r ∈ Icc c xHi, lowPrimitive lam d r = cap lam d.S c+∫ t in c..r, psi t) :
    ∀ᵐ r ∂volume.restrict (Ioo c xHi), HasDerivAt psi (deriv psi r) r ∧
      (deriv psi r = -1 ∨ ∃ z ∈ Icc zStart zEnd, ∃ v ∈ controlFeatureSupport d,
        featureH hd z (continuation lam d z) v = vectorField lam d z (continuation lam d z) ∧
        (deriv psi r = -featureTheta lam d v ∨
          (v.1.1 = r ∧ v.1.2.2 = r ∧ v.1.2.1 ≤ r ∧ r ∈ Ioo pLo pHi ∧
            deriv psi r = diagonalFeatureSlope lam d z (continuation lam d z) v r (psi r)))) := by
  filter_upwards [minimizer_slope_classification_strong hd hl hmin hpass hc hlast hpsi heq hprimitive]
    with r hr
  exact ⟨hr.1,hr.2.imp (fun h => h.2) id⟩

end OptimalG.Variational
