import OptimalG.VariationalCapSelection

/-! Actual high-rank continuation preservation under low-rank cap replacement.
The comparison consists of two finite rank replacements and one finite primitive
replacement, followed by essential-infimum and scalar ODE comparison. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem feature_le_of_primitive_le {lam z u A B : ℝ} {d d' : LowRankData}
    (hd : Admissible lam d) (hd' : Admissible lam d') (hS : d'.S = d.S)
    {v : Control} (hv : v ∈ controlDomain) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d'.S)
    (hA : A ≤ lam-v.2.1) (hB : B ≤ lam-v.2.2)
    (hactive : featureH hd' z u (v,A,B) ≤ lam-z)
    (hR : primitive lam d v.1 ≤ primitive lam d' v.1) :
    featureH hd z u (v,A,B) ≤ featureH hd' z u (v,A,B) := by
  have ha := hd'.feature_alpha_positive hv hz huLow huHigh hA hB hactive
  have hc := (hd'.control_coefficients_positive hv hz huLow huHigh).2
  have hD : 0 < Certificates.Control.det (2*lam-v.2.1) (v.1+v.2.2-lam)
      (primitive lam d' v.1) (quadratic lam (1-v.1)-d.S) := by
    rw [← hS]
    change 0 < controlDeterminant lam d' v
    linarith [hd'.determinant_positive hv]
  have hD' : 0 < Certificates.Control.det (2*lam-v.2.1) (v.1+v.2.2-lam)
      (primitive lam d v.1) (quadratic lam (1-v.1)-d.S) := by
    change 0 < controlDeterminant lam d v
    linarith [hd.determinant_positive hv]
  have hval := Certificates.Control.value_R_decrease_nonincreasing (z-lam) (2*lam-v.2.1)
    (v.1+v.2.2-lam) (primitive lam d' v.1) (primitive lam d v.1)
    (quadratic lam (1-v.1)-d.S) (quadratic lam (z-v.1)-d.S-u) A B hD hD' hR ha.le
    (by rw [hS] at hc; linarith)
  rw [featureH_eq_value hd z u A B hv,featureH_eq_value hd' z u A B hv,hS]
  exact hval

theorem original_field_le_replaced_feature {lam c z u A B : ℝ} {d d' : LowRankData}
    (hd : Admissible lam d) (hd' : Admissible lam d') (hS : d'.S = d.S)
    (hc : c ∈ Icc ell tEnd) (hcx : c ≤ xHi)
    (hcontact : lowPrimitive lam d c = cap lam d.S c)
    (hR : ∀ p ∈ Icc pLo pHi, primitive lam d p ≤ primitive lam d' p)
    {v : Control} (hv : v ∈ controlDomain) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d'.S)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hsourceA : (v.2.1,A) ∈ rankScoreSupport d.phi ∨ (v.2.1 < c ∧ A = capScore lam d.S v.2.1))
    (hsourceB : (v.2.2,B) ∈ rankScoreSupport d.phi ∨ (v.2.2 < c ∧ B = capScore lam d.S v.2.2)) :
    vectorField lam d z u ≤ featureH hd' z u (v,A,B) := by
  by_cases hline : featureH hd' z u (v,A,B) ≤ lam-z
  · obtain ⟨w,hw,hp,hselect⟩ := select_original_feature hd hd' hS hc hcx hcontact hv hz huLow huHigh
      hA0 hB0 hsourceA hsourceB
    have hwdom := (hd.controlFeatureSupport_subset hw).1
    have hwx := (hd.rankScoreSupport_bounds (hd.featureSupport_rankScores hw).1).2.2
    have hwy := (hd.rankScoreSupport_bounds (hd.featureSupport_rankScores hw).2).2.2
    have hcompare := feature_le_of_primitive_le hd hd' hS hwdom hz huLow huHigh hwx hwy
      (hselect.trans hline) (hR w.1.1 hwdom.1)
    exact ((min_le_right _ _).trans (hd.essInf_le_featureH z u hw)).trans (hcompare.trans hselect)
  · exact (vectorField_le_line lam d z u).trans (le_of_not_ge hline)

theorem capReplacement_vectorField_ge {lam c z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : c ∈ Ioc ell tEnd) (hcx : c ≤ xHi)
    (hcontact : lowPrimitive lam d c = cap lam d.S c)
    (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S) :
    vectorField lam d z u ≤ vectorField lam (capReplacement lam d c) z u := by
  let d' := capReplacement lam d c
  have hd' : Admissible lam d' := capReplacement_admissible hd hc hcontact
  have hc' : c ∈ Icc ell tEnd := ⟨hc.1.le,hc.2⟩
  have hne : ∀ᵐ r ∂volume.restrict (Icc ell tEnd), r ≠ c := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simp
  apply le_min (vectorField_le_line lam d z u)
  apply le_essInf_of_ae_le _ _ (hd'.controlH_bounded z u).boundedAbove.isCoboundedUnder_ge
  filter_upwards [ae_restrict_mem controlDomain_measurable,
    ae_control_lowRanks _ hd.ae_low_rankScore_mem,
    ae_control_lowRanks _ hd'.2.2.2.1,ae_control_lowRanks _ hne]
    with v hv hgraph hbounds hne
  rw [← featureH_map_eq hd' z u hv]
  have hsource (r : ℝ) (hr : r ∈ Icc xLo xHi) (hne : r ≠ c)
      (hg : (r,d.phi r) ∈ rankScoreSupport d.phi) :
      (r,d'.phi r) ∈ rankScoreSupport d.phi ∨ (r < c ∧ d'.phi r = capScore lam d.S r) := by
    by_cases hrc : r < c
    · exact Or.inr ⟨hrc,piecewise_eq_of_mem (Iic c) _ _ hrc.le⟩
    · have hcr : c < r := lt_of_le_of_ne (le_of_not_gt hrc) (Ne.symm hne)
      have he : d'.phi r = d.phi r := piecewise_eq_of_notMem (Iic c) _ _ (not_le.mpr hcr)
      exact Or.inl (by rwa [he])
  exact original_field_le_replaced_feature hd hd' rfl hc' hcx hcontact
    (fun p hp => primitive_le_capReplacement hd hc' hcontact hp) hv hz huLow huHigh
    hbounds.1.1 hbounds.2.1
    (hsource _ hv.2.1 hne.1 (hgraph.1 hv.2.1))
    (hsource _ ⟨(le_max_left _ _).trans hv.2.2.1,hv.2.2.2⟩ hne.2
      (hgraph.2 ⟨(le_max_left _ _).trans hv.2.2.1,hv.2.2.2⟩))

/-- The cap-replaced actual ODE lies above the original feasible continuation. -/
theorem capReplacement_continuation_ge {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : c ∈ Ioc ell tEnd) (hcx : c ≤ xHi)
    (hcontact : lowPrimitive lam d c = cap lam d.S c)
    (hpass : PassesTerminalTests lam d (continuation lam d)) :
    ∀ z ∈ Icc zStart zEnd, continuation lam d z ≤ continuation lam (capReplacement lam d c) z := by
  have hd' := capReplacement_admissible hd hc hcontact
  have hfield : ∀ z ∈ Icc zStart zEnd,
      vectorField lam d z (continuation lam d z) ≤
      vectorField lam (capReplacement lam d c) z (continuation lam d z+0) := by
    intro z hz
    rw [add_zero]
    apply capReplacement_vectorField_ge hd hc hcx hcontact hz
    · linarith [hd.continuation_above_root_budget hd.isContinuation hpass hz]
    · exact hd.continuation_le_quadratic hd.isContinuation z hz
  simpa only [add_zero] using hd'.continuation_shift_of_field_comparison (q:=0) (by simp [capReplacement]) hfield hd

theorem capReplacement_passesTerminalTests {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : c ∈ Ioc ell tEnd) (hcx : c ≤ xHi)
    (hcontact : lowPrimitive lam d c = cap lam d.S c)
    (hpass : PassesTerminalTests lam d (continuation lam d)) :
    PassesTerminalTests lam (capReplacement lam d c) (continuation lam (capReplacement lam d c)) := by
  intro z hz q hq
  have hY := capReplacement_continuation_ge hd hc hcx hcontact hpass z
    ⟨(by norm_num [zStart,zTest] : zStart ≤ zTest).trans hz.1,hz.2⟩
  exact (hpass z hz q hq).trans hY

end OptimalG.Variational
