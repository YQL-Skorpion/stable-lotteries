import OptimalG.VariationalRepresentativeGraph
import OptimalG.VariationalContactLocation
import OptimalG.VariationalAEData

/-! Actual score regularity of an interior minimizing pair. The representative
has a genuine classical primitive on the free interval above the final contact. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

private theorem continuous_antitone_Icc {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : Continuous f) (hm : AntitoneOn f (Ioo a b)) : AntitoneOn f (Icc a b) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with he | hxy
  · rw [he]
  let m := (x+y)/2
  have hxm : x < m := by dsimp [m]; linarith
  have hmy : m < y := by dsimp [m]; linarith
  have ham : a < m := hx.1.trans_lt hxm
  have hmb : m < b := hmy.trans_le hy.2
  have hleft : Ioo a m ⊆ {t | f m ≤ f t} := by
    intro t ht
    exact hm ⟨ht.1,ht.2.trans hmb⟩ ⟨ham,hmb⟩ ht.2.le
  have hright : Ioo m b ⊆ {t | f t ≤ f m} := by
    intro t ht
    exact hm ⟨ham,hmb⟩ ⟨ham.trans ht.1,ht.2⟩ ht.1.le
  have hleft' := closure_minimal hleft (isClosed_le continuous_const hf)
  have hright' := closure_minimal hright (isClosed_le hf continuous_const)
  rw [closure_Ioo ham.ne] at hleft'
  rw [closure_Ioo hmb.ne] at hright'
  exact (hright' ⟨hmy.le,hy.2⟩).trans (hleft' ⟨hx.1,hxm.le⟩)

theorem minimizer_regular_interval {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Icc ell tEnd) (hcontact : lowPrimitive lam d c = cap lam d.S c)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c) :
    c ∈ Ico xLo xHi ∧ ∃ L : ℝ≥0, ∃ ψ : ℝ → ℝ,
      LipschitzWith L ψ ∧ AntitoneOn ψ (Icc c xHi) ∧
      d.phi =ᵐ[volume.restrict (Icc c xHi)] ψ ∧
      (∀ r ∈ Icc c xHi, (r,ψ r) ∈ rankScoreSupport d.phi) ∧
      (∀ r ∈ Icc c xHi, 0 ≤ ψ r ∧ ψ r ≤ lam-r) ∧
      (∀ r ∈ Icc c xHi, lowPrimitive lam d r = cap lam d.S c+∫ t in c..r, ψ t) := by
  have hcI := minimizer_last_contact_in_test_interval hd hl hmin hpass hc hcontact hlast
  obtain ⟨L,ψ,hψ,hm,heq⟩ := minimizer_regular_representative hd hl hmin hpass hc hlast
  rw [max_eq_left hcI.1] at hm heq
  have heq' : d.phi =ᵐ[volume.restrict (Icc c xHi)] ψ := by
    simpa only [restrict_Ioo_eq_restrict_Icc] using heq
  have hg : ∀ r ∈ Icc c xHi, (r,ψ r) ∈ rankScoreSupport d.phi :=
    fun r hr => hd.continuous_rep_score_mem hcI.2 hcI.1 le_rfl hψ.continuous heq hr
  refine ⟨hcI,L,ψ,hψ,continuous_antitone_Icc hcI.2 hψ.continuous hm,heq',hg,?_,?_⟩
  · intro r hr
    exact (hd.rankScoreSupport_bounds (hg r hr)).2
  · intro r hr
    have hr' : r ∈ Icc ell tEnd := ⟨hc.1.trans hr.1,hr.2.trans (by norm_num [xHi,tEnd])⟩
    have hi := hd.lowPrimitive_sub hc hr'
    have heqr : d.phi =ᵐ[volume.restrict (Ioc c r)] ψ :=
      ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hr.2)) heq'
    have hieq := intervalIntegral.integral_congr_ae_restrict (μ := volume) (a := c) (b := r)
      (by simpa only [uIoc_of_le hr.1] using heqr)
    rw [hcontact,hieq] at hi
    linarith

/-- Genuine differentiability of the minimizing primitive on its free interval,
with the continuous representative as derivative. -/
theorem hasDerivAt_lowPrimitive_of_rep {lam c b r : ℝ} {d : LowRankData} {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) (hr : r ∈ Ioo c b)
    (hprimitive : ∀ t ∈ Icc c b, lowPrimitive lam d t = cap lam d.S c+∫ u in c..t,ψ u) :
    HasDerivAt (lowPrimitive lam d) (ψ r) r := by
  have hd := (intervalIntegral.integral_hasDerivAt_right (hψ.intervalIntegrable c r)
    (hψ.stronglyMeasurableAtFilter volume (𝓝 r)) hψ.continuousAt).const_add (cap lam d.S c)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
  exact hprimitive t ⟨ht.1.le,ht.2.le⟩

end OptimalG.Variational
