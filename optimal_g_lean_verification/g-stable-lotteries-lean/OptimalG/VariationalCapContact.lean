import OptimalG.VariationalInactiveSet

/-! Last low-rank cap contact and saturation away from tested ranks. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

theorem cap_continuous_lowInterval (lam S : ℝ) : ContinuousOn (cap lam S) (Icc ell tEnd) := by
  unfold cap
  apply ContinuousOn.sub (by fun_prop)
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro r hr
  have hh := hr.2
  norm_num [tEnd] at hh
  linarith

/-- The last cap contact is attained, since the true primitive is continuous. -/
theorem Admissible.exists_last_cap_contact {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    ∃ c ∈ Icc ell tEnd, lowPrimitive lam d c = cap lam d.S c ∧
      ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c := by
  let E : Set LowRankInterval := {r | lowPrimitive lam d r = cap lam d.S r}
  have hc : IsClosed E := isClosed_eq
    (continuousOn_iff_continuous_restrict.mp hd.lowPrimitive_lipschitz.continuousOn)
    (continuousOn_iff_continuous_restrict.mp (cap_continuous_lowInterval lam d.S))
  have hne : E.Nonempty := by
    refine ⟨⟨ell, by norm_num [ell,tEnd]⟩, ?_⟩
    exact lowPrimitive_at_ell lam d
  obtain ⟨c,hcE,hmax⟩ := hc.isCompact.exists_isMaxOn hne continuous_subtype_val.continuousOn
  refine ⟨c,c.property,hcE,?_⟩
  intro r hr heq
  exact hmax (show (⟨r,hr⟩ : LowRankInterval) ∈ E from heq)

/-- Strict cap slack has a positive uniform margin on every closed interval
strictly to the right of the last contact. -/
theorem Admissible.cap_margin_after_contact {lam c a : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : c ∈ Icc ell tEnd)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c)
    (hca : c < a) (hate : a ≤ tEnd) :
    ∃ m > 0, ∀ r ∈ Icc a tEnd, lowPrimitive lam d r+m ≤ cap lam d.S r := by
  have hsub : Icc a tEnd ⊆ Icc ell tEnd := Icc_subset_Icc (hc.1.trans hca.le) le_rfl
  have hcont := ((cap_continuous_lowInterval lam d.S).sub hd.lowPrimitive_lipschitz.continuousOn).mono hsub
  obtain ⟨r,hr,hm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hate) hcont
  have hpos : 0 < cap lam d.S r-lowPrimitive lam d r := by
    apply lt_of_le_of_ne (sub_nonneg.mpr (hd.lowPrimitive_le_cap (hsub hr)))
    intro heq
    have hcontact : lowPrimitive lam d r = cap lam d.S r := by linarith
    have hrc := hlast r (hsub hr) hcontact
    linarith [hr.1]
  refine ⟨cap lam d.S r-lowPrimitive lam d r,hpos,?_⟩
  intro s hs
  have hh := hm hs
  dsimp at hh
  linarith

/-- Outside the tested score interval, every rank after the last cap contact
saturates the line bound almost everywhere. This is the second conclusion of
Lemma B.1, derived from actual admissible perturbations. -/
theorem minimizer_saturates_outside_test_interval {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Icc ell tEnd)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c) :
    ∀ᵐ r ∂volume.restrict (Icc ell tEnd), c < r → r ∉ Icc xLo xHi → d.phi r = lam-r := by
  rcases eq_or_lt_of_le hc.2 with hceq | hclt
  · subst c
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    intro hcr _
    exact (not_lt_of_ge hr.2 hcr).elim
  obtain ⟨an,_,han,hat⟩ := exists_seq_strictAnti_tendsto' hclt
  have hs (n : ℕ) : ∀ᵐ r ∂volume.restrict (Icc ell tEnd),
      r ∈ Ioi (an n) \ Icc xLo xHi → d.phi r = lam-r := by
    obtain ⟨m,hm,hcap⟩ := hd.cap_margin_after_contact hc hlast (han n).1 (han n).2.le
    apply inactive_set_saturates hd hl hmin hpass
      (measurableSet_Ioi.diff measurableSet_Icc) (fun _ hr => hr.1) hm hcap
      (by norm_num : (0 : ℝ) < 1)
    intro z hz
    filter_upwards [ae_restrict_mem controlDomain_measurable] with v hv
    intro he
    rcases he with he | he
    · exact (he.2 hv.2.1).elim
    · exact (he.2 ⟨(le_max_left _ _).trans hv.2.2.1,hv.2.2.2⟩).elim
  filter_upwards [ae_all_iff.mpr hs] with r hr
  intro hcr hnot
  obtain ⟨n,hn⟩ := ((tendsto_order.mp hat).2 r hcr).exists
  exact hr n ⟨hn,hnot⟩

end OptimalG.Variational
