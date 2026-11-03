import OptimalG.VariationalRegularRepresentative

/-! Continuous representatives recover pointwise graph support and monotonicity. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

private theorem mem_support_restrict_open {a b r : ℝ} (hr : r ∈ Ioo a b) :
    r ∈ (volume.restrict (Ioo a b)).support := by
  apply Measure.interior_inter_support
  refine ⟨?_,?_⟩
  · simpa only [isOpen_Ioo.interior_eq] using hr
  · simp only [Measure.support_eq_univ,mem_univ]

private theorem mem_support_restrict_open_closed {a b r : ℝ} (hab : a < b) (hr : r ∈ Icc a b) :
    r ∈ (volume.restrict (Ioo a b)).support := by
  have hsub : Ioo a b ⊆ (volume.restrict (Ioo a b)).support := fun _ h => mem_support_restrict_open h
  have hh := closure_minimal hsub (volume.restrict (Ioo a b)).isClosed_support
  rw [closure_Ioo hab.ne] at hh
  exact hh hr

theorem Admissible.continuous_rep_score_mem {lam a b : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hab : a < b) (ha : xLo ≤ a) (hb : b ≤ xHi)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (heq : d.phi =ᵐ[volume.restrict (Ioo a b)] ψ) {r : ℝ} (hr : r ∈ Icc a b) :
    (r,ψ r) ∈ rankScoreSupport d.phi := by
  have hsub : Ioo a b ⊆ Icc ell tEnd := by
    intro t ht
    exact ⟨(by norm_num [ell,xLo] : ell ≤ xLo).trans (ha.trans ht.1.le),
      ht.2.le.trans (hb.trans (by norm_num [xHi,tEnd]))⟩
  have hclosed : IsClosed {r : ℝ | (r,ψ r) ∈ rankScoreSupport d.phi} :=
    (rankScoreMeasure d.phi).isClosed_support.preimage (continuous_id.prodMk hψ)
  apply (volume.restrict (Ioo a b)).support_subset_of_isClosed hclosed _ (mem_support_restrict_open_closed hab hr)
  filter_upwards [heq,ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset hsub hd.ae_low_rankScore_mem] with t ht htab hg
  rw [← ht]
  exact hg ⟨ha.trans htab.1.le,htab.2.le.trans hb⟩

theorem minimizer_continuous_rep_antitone {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Icc ell tEnd)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (heq : d.phi =ᵐ[volume.restrict (Ioo (max c xLo) xHi)] ψ) :
    AntitoneOn ψ (Ioo (max c xLo) xHi) := by
  intro r hr s hs hrs
  rcases eq_or_lt_of_le hrs with he | hrs
  · rw [he]
  have hab : max c xLo < xHi := hr.1.trans hr.2
  have hsG := hd.continuous_rep_score_mem hab (le_max_right _ _) le_rfl hψ heq ⟨hs.1.le,hs.2.le⟩
  have hright := minimizer_ae_antitone_after_contact hd hl hmin hpass hc hlast
  have hsub : Ioo (max c xLo) s ⊆ Icc ell tEnd := by
    intro t ht
    exact ⟨hc.1.trans ((le_max_left _ _).trans ht.1.le),
      ht.2.le.trans (hs.2.le.trans (by norm_num [xHi,tEnd]))⟩
  have hsub' : Ioo (max c xLo) s ⊆ Ioo (max c xLo) xHi := Ioo_subset_Ioo le_rfl hs.2.le
  have hclosed : IsClosed {t : ℝ | ψ s ≤ ψ t} := isClosed_le continuous_const hψ
  apply (volume.restrict (Ioo (max c xLo) s)).support_subset_of_isClosed hclosed _
    (mem_support_restrict_open ⟨hr.1,hrs⟩)
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset hsub hright,
    ae_restrict_of_ae_restrict_of_subset hsub' heq] with t ht hrt he
  have hh := hrt ((le_max_left _ _).trans_lt ht.1) (s,ψ s) hsG ht.2.le
  rwa [he] at hh

/-- A measurable minimizer has a true Lipschitz, nonincreasing representative
on the tested interval above its last cap contact. No numerical tube estimates
or pre-existing score regularity are assumed. -/
theorem minimizer_regular_representative {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Icc ell tEnd)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c) :
    ∃ L : ℝ≥0, ∃ ψ : ℝ → ℝ, LipschitzWith L ψ ∧
      AntitoneOn ψ (Ioo (max c xLo) xHi) ∧
      d.phi =ᵐ[volume.restrict (Ioo (max c xLo) xHi)] ψ := by
  obtain ⟨L,ψ,hψ,heq⟩ := minimizer_lipschitz_representative hd hl hmin hpass hc hlast
  exact ⟨L,ψ,hψ,minimizer_continuous_rep_antitone hd hl hmin hpass hc hlast hψ.continuous heq,heq⟩

end OptimalG.Variational
