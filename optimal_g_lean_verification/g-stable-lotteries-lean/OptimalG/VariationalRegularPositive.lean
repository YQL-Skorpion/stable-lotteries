import OptimalG.VariationalRegularity
import OptimalG.VariationalPositiveScores

/-! Positive continuous representatives above the final cap contact. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem minimizer_score_positive_after_contact {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Icc ell tEnd)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c) :
    ∀ᵐ r ∂volume.restrict (Icc ell tEnd), c < r → (7:ℝ)/100 < d.phi r := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    minimizer_active_rank_attained hd hl hmin hpass hc hlast] with r hr ha
  intro hcr
  by_cases heq : d.phi r = lam-r
  · rw [heq]
    have hL := hd.1.1
    have hr1 := hr.2
    norm_num [lambdaLo,tEnd] at hL hr1
    linarith
  · obtain ⟨z,hz,v,hv,hactive,hmatch⟩ := ha hcr heq
    have huLow : quadratic lam z-quadratic lam 1 ≤ continuation lam d z := by
      linarith [hd.continuation_above_root_budget hd.isContinuation hpass hz]
    have huHigh := hd.continuation_le_quadratic hd.isContinuation z hz
    have hb := active_feature_scores_positive hd hz huLow huHigh hv hactive
    rcases hmatch with hx | hy
    · simpa only [hx.2] using hb.1
    · simpa only [hy.2] using hb.2

private theorem continuous_ae_lower_Icc {a b B : ℝ} {ψ : ℝ → ℝ}
    (hab : a < b) (hψ : Continuous ψ) (h : ∀ᵐ r ∂volume.restrict (Ioo a b), B ≤ ψ r) :
    ∀ r ∈ Icc a b, B ≤ ψ r := by
  have hsupport : Ioo a b ⊆ (volume.restrict (Ioo a b)).support := by
    intro r hr
    apply Measure.interior_inter_support
    refine ⟨?_,?_⟩
    · simpa only [isOpen_Ioo.interior_eq] using hr
    · simp only [Measure.support_eq_univ,mem_univ]
  have hsupport' := closure_minimal hsupport (volume.restrict (Ioo a b)).isClosed_support
  rw [closure_Ioo hab.ne] at hsupport'
  exact fun r hr => (volume.restrict (Ioo a b)).support_subset_of_isClosed
    (isClosed_le continuous_const hψ) h (hsupport' hr)

theorem minimizer_continuous_rep_positive {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Icc ell tEnd) (hcx : c < xHi)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (heq : d.phi =ᵐ[volume.restrict (Ioo c xHi)] ψ) :
    ∀ r ∈ Icc c xHi, (7:ℝ)/100 ≤ ψ r := by
  apply continuous_ae_lower_Icc hcx hψ
  have hsub : Ioo c xHi ⊆ Icc ell tEnd :=
    Ioo_subset_Icc_self.trans (Icc_subset_Icc hc.1 (by norm_num [xHi,tEnd]))
  filter_upwards [ae_restrict_mem measurableSet_Ioo,heq,
    ae_restrict_of_ae_restrict_of_subset hsub
      (minimizer_score_positive_after_contact hd hl hmin hpass hc hlast)] with r hr he hpos
  rw [← he]
  exact (hpos hr.1).le

end OptimalG.Variational
