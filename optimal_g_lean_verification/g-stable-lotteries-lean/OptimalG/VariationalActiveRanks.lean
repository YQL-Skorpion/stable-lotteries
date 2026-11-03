import OptimalG.VariationalActiveFeatures

/-! The active-rank condition from actual admissible finite perturbations. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

/-- A score pair separated from all active features must saturate the line
bound wherever there is a uniform cap margin to its right. -/
theorem minimizer_active_score_or_saturated_of_cap_margin {lam a m : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hm : 0 < m) (hcap : ∀ r ∈ Icc a tEnd, lowPrimitive lam d r+m ≤ cap lam d.S r) :
    ∀ᵐ r ∂volume.restrict (Icc ell tEnd), a < r →
      d.phi r = lam-r ∨ (r,d.phi r) ∈ activeScoreSet hd := by
  have hsat (ε : ℝ) (hε : 0 < ε) :
      ∀ᵐ r ∂volume.restrict (Icc ell tEnd), a < r →
        ε ≤ activeScoreGap hd (r,d.phi r) → d.phi r = lam-r := by
    let E : Set ℝ := Ioi a ∩ {r | ε ≤ activeScoreGap hd (r,d.phi r)}
    have hgraph : AEMeasurable (fun r : ℝ => (r,d.phi r)) (volume.restrict (Icc ell tEnd)) :=
      measurable_id.aemeasurable.prodMk hd.2.2.1.aestronglyMeasurable.aemeasurable
    have hE : NullMeasurableSet E (volume.restrict (Icc ell tEnd)) :=
      measurableSet_Ioi.nullMeasurableSet.inter (nullMeasurableSet_le aemeasurable_const
        ((activeScoreGap_continuous hd).measurable.comp_aemeasurable hgraph))
    obtain ⟨δ,hδ,hmargin⟩ := activeScoreGap_control_margin hd hε
    have hh := inactive_nullMeasurable_set_saturates hd hl hmin hpass hE
      (fun _ hr => hr.1) hm hcap hδ ?_
    · filter_upwards [hh] with r hr
      exact fun har hgap => hr ⟨har,hgap⟩
    · intro z hz
      filter_upwards [hd.ae_mem_controlFeatureSupport,ae_restrict_mem controlDomain_measurable] with c hc hdom
      intro htouch
      have hg : ε ≤ activeScoreGap hd (c.2.1,d.phi c.2.1) ∨
          ε ≤ activeScoreGap hd (c.2.2,d.phi c.2.2) := htouch.imp And.right And.right
      have hh := hmargin (⟨z,hz⟩,controlFeatureMap d c) hc hg
      dsimp only [featureTrajectorySlack] at hh
      rw [featureH_map_eq hd z (continuation lam d z) hdom] at hh
      linarith
  have hall : ∀ᵐ r ∂volume.restrict (Icc ell tEnd), ∀ n : ℕ,
      a < r → 1/((n:ℝ)+1) ≤ activeScoreGap hd (r,d.phi r) → d.phi r = lam-r :=
    ae_all_iff.mpr fun n => hsat (1/((n:ℝ)+1)) (by positivity)
  filter_upwards [hall] with r hr
  intro har
  by_cases hactive : (r,d.phi r) ∈ activeScoreSet hd
  · exact Or.inr hactive
  · left
    have hpos : 0 < activeScoreGap hd (r,d.phi r) :=
      lt_of_le_of_ne (activeScoreGap_nonneg hd _) (fun hh => hactive ((activeScoreGap_eq_zero_iff hd _).mp hh.symm))
    obtain ⟨n,hn⟩ := ((tendsto_order.mp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2
      (activeScoreGap hd (r,d.phi r)) hpos).exists
    exact hr n har hn.le

/-- Almost every rank above the final cap contact either saturates the line or
occurs, with its actual score value, in an attained active support control. This
holds before selecting any continuous representative of the score. -/
theorem minimizer_active_score_or_saturated {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Icc ell tEnd)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c) :
    ∀ᵐ r ∂volume.restrict (Icc ell tEnd), c < r →
      d.phi r = lam-r ∨ (r,d.phi r) ∈ activeScoreSet hd := by
  rcases eq_or_lt_of_le hc.2 with he | hlt
  · subst c
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    intro hcr
    exact (not_lt_of_ge hr.2 hcr).elim
  obtain ⟨an,_,han,hat⟩ := exists_seq_strictAnti_tendsto' hlt
  have hs (n : ℕ) : ∀ᵐ r ∂volume.restrict (Icc ell tEnd), an n < r →
      d.phi r = lam-r ∨ (r,d.phi r) ∈ activeScoreSet hd := by
    obtain ⟨m,hm,hcap⟩ := hd.cap_margin_after_contact hc hlast (han n).1 (han n).2.le
    exact minimizer_active_score_or_saturated_of_cap_margin hd hl hmin hpass hm hcap
  filter_upwards [ae_all_iff.mpr hs] with r hr
  intro hcr
  obtain ⟨n,hn⟩ := ((tendsto_order.mp hat).2 r hcr).exists
  exact hr n hn

theorem minimizer_active_rank_attained {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Icc ell tEnd)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c) :
    ∀ᵐ r ∂volume.restrict (Icc ell tEnd), c < r → d.phi r ≠ lam-r →
      ∃ z ∈ Icc zStart zEnd, ∃ v ∈ controlFeatureSupport d,
        featureH hd z (continuation lam d z) v = vectorField lam d z (continuation lam d z) ∧
        ((v.1.2.1 = r ∧ v.2.1 = d.phi r) ∨ (v.1.2.2 = r ∧ v.2.2 = d.phi r)) := by
  filter_upwards [minimizer_active_score_or_saturated hd hl hmin hpass hc hlast] with r hr
  intro hcr hneq
  have hm := (hr hcr).resolve_left hneq
  rcases hm with ⟨w,hw,he⟩ | ⟨w,hw,he⟩
  · refine ⟨w.1,w.1.property,w.2,hw.1.2,sub_eq_zero.mp hw.2,Or.inl ?_⟩
    exact Prod.mk.inj he
  · refine ⟨w.1,w.1.property,w.2,hw.1.2,sub_eq_zero.mp hw.2,Or.inr ?_⟩
    exact Prod.mk.inj he

end OptimalG.Variational
