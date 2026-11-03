import OptimalG.VariationalLeftSupport

/-! A genuine Lipschitz representative of the minimizing low score above its
last cap contact, obtained before the sharp tube-dependent shape estimates. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem minimizer_ae_left_bound {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Icc ell tEnd)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c) :
    ∃ L : ℝ≥0, 1 ≤ L ∧ ∀ᵐ r ∂volume.restrict (Icc ell tEnd), c < r →
      ∀ w ∈ rankScoreSupport d.phi, w.1 ≤ r → w.2-d.phi r ≤ L*(r-w.1) := by
  obtain ⟨K,hK⟩ := hd.exists_active_y_left_bound
  let L := max (1:ℝ≥0) K
  have hL1 : (1:ℝ) ≤ L := le_max_left _ _
  have hLK : (K:ℝ) ≤ L := le_max_right _ _
  refine ⟨L,le_max_left _ _,?_⟩
  filter_upwards [minimizer_active_rank_attained hd hl hmin hpass hc hlast] with r hr
  intro hcr w hw hwr
  have hdelta : 0 ≤ r-w.1 := sub_nonneg.mpr hwr
  by_cases heq : d.phi r = lam-r
  · have hceil := (hd.rankScoreSupport_bounds hw).2.2
    have hm := mul_le_mul_of_nonneg_right hL1 hdelta
    rw [heq]
    linarith
  · obtain ⟨z,hz,v,hv,hactive,hmatch⟩ := hr hcr heq
    have huLow : quadratic lam z-quadratic lam 1 ≤ continuation lam d z := by
      linarith [hd.continuation_above_root_budget hd.isContinuation hpass hz]
    have huHigh := hd.continuation_le_quadratic hd.isContinuation z hz
    rcases hmatch with hx | hy
    · have hs := active_feature_supports_x hd hz huLow huHigh hv hactive hw
      rw [hx.1,hx.2] at hs
      have hθ := (hd.featureTheta_bounds hv).2.le
      have hm := mul_le_mul_of_nonneg_right (hθ.trans hL1) hdelta
      nlinarith only [hs,hm]
    · have hwv : w.1 ≤ v.1.2.2 := by rwa [hy.1]
      have hs := hK z hz (continuation lam d z) huLow huHigh v hv hactive w hw hwv
      rw [hy.1,hy.2] at hs
      exact hs.trans (mul_le_mul_of_nonneg_right hLK hdelta)

/-- The minimizing measurable score agrees almost everywhere with an actual
globally Lipschitz function on the tested interval above its final cap contact. -/
theorem minimizer_lipschitz_representative {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Icc ell tEnd)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c) :
    ∃ L : ℝ≥0, ∃ ψ : ℝ → ℝ, LipschitzWith L ψ ∧
      d.phi =ᵐ[volume.restrict (Ioo (max c xLo) xHi)] ψ := by
  obtain ⟨L,_,hleft⟩ := minimizer_ae_left_bound hd hl hmin hpass hc hlast
  have hright := minimizer_ae_antitone_after_contact hd hl hmin hpass hc hlast
  let E : Set ℝ := {r | r ∈ Ioo (max c xLo) xHi ∧ (r,d.phi r) ∈ rankScoreSupport d.phi ∧
    (∀ w ∈ rankScoreSupport d.phi, w.1 ≤ r → w.2-d.phi r ≤ L*(r-w.1)) ∧
    (∀ w ∈ rankScoreSupport d.phi, r ≤ w.1 → w.2 ≤ d.phi r)}
  have hLip : LipschitzOnWith L d.phi E := by
    apply LipschitzOnWith.of_dist_le_mul
    intro r hr s hs
    wlog hrs : r ≤ s generalizing r s
    · simpa only [dist_comm] using this s hs r hr (le_of_not_ge hrs)
    have hmono := hr.2.2.2 (s,d.phi s) hs.2.1 hrs
    have hdrop := hs.2.2.1 (r,d.phi r) hr.2.1 hrs
    rw [Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hmono),abs_of_nonpos (sub_nonpos.mpr hrs)]
    simpa only [neg_sub] using hdrop
  obtain ⟨ψ,hψ,heq⟩ := hLip.extend_real
  refine ⟨L,ψ,hψ,?_⟩
  have hsub : Ioo (max c xLo) xHi ⊆ Icc ell tEnd := by
    intro r hr
    exact ⟨hc.1.trans ((le_max_left _ _).trans hr.1.le),
      hr.2.le.trans (by norm_num [xHi,tEnd])⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset hsub hd.ae_low_rankScore_mem,
    ae_restrict_of_ae_restrict_of_subset hsub hleft,
    ae_restrict_of_ae_restrict_of_subset hsub hright] with r hr hgraph hleft hright
  have hcr : c < r := (le_max_left _ _).trans_lt hr.1
  have hrI : r ∈ Icc xLo xHi := ⟨(le_max_right _ _).trans hr.1.le,hr.2.le⟩
  exact heq ⟨hr,hgraph hrI,hleft hcr,hright hcr⟩

end OptimalG.Variational
