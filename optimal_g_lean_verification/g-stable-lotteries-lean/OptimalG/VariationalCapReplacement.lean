import OptimalG.VariationalCapSlope

/-! Replacing the primitive by the cap below a genuine contact preserves every
low-rank admissibility condition. Continuation feasibility is a separate lemma. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

noncomputable def capReplacement (lam : ℝ) (d : LowRankData) (c : ℝ) : LowRankData :=
  ⟨d.S, (Iic c).piecewise (capScore lam d.S) d.phi⟩

theorem Admissible.capScore_memLp {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    MemLp (capScore lam d.S) ⊤ (volume.restrict (Icc ell tEnd)) := by
  have hm : Measurable (capScore lam d.S) := by unfold capScore; fun_prop
  apply memLp_top_of_bound hm.aestronglyMeasurable 1
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  rw [Real.norm_eq_abs,abs_of_nonneg (hd.capScore_pos hr).le]
  have hL : lam ≤ 1 := by have hh := hd.1.2; norm_num [lambdaHi] at hh; linarith
  have hL0 : 0 ≤ lam := by have hh := hd.1.1; norm_num [lambdaLo] at hh; linarith
  have hS0 : 0 ≤ d.S := by linarith [hd.slack_lower]
  have hfrac := div_nonneg (mul_nonneg hL0 hS0) (sq_nonneg (1-r))
  unfold capScore
  linarith

theorem Admissible.capReplacement_memLp {lam c : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    MemLp (capReplacement lam d c).phi ⊤ (volume.restrict (Icc ell tEnd)) :=
  MemLp.piecewise measurableSet_Iic (hd.capScore_memLp.restrict _) (hd.2.2.1.restrict _)

private theorem replacement_intervalIntegrable {lam c a b : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (ha : ell ≤ a) (hab : a ≤ b) (hb : b ≤ tEnd) :
    IntervalIntegrable (capReplacement lam d c).phi volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  have hi : IntegrableOn (capReplacement lam d c).phi (Icc ell tEnd) :=
    MemLp.integrable (by simp) hd.capReplacement_memLp
  exact hi.mono_set (Icc_subset_Icc ha hb)

theorem integral_capScore {lam a b : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (ha : ell ≤ a) (hab : a ≤ b) (hb : b ≤ tEnd) :
    (∫ r in a..b,capScore lam d.S r) = cap lam d.S b-cap lam d.S a := by
  have hi0 : IntegrableOn (capScore lam d.S) (Icc ell tEnd) :=
    MemLp.integrable (by simp) hd.capScore_memLp
  have hi : IntervalIntegrable (capScore lam d.S) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (hi0.mono_set (Icc_subset_Icc ha hb))
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
  intro r hr
  have hr' : r ∈ Icc a b := by simpa only [uIcc_of_le hab] using hr
  apply cap_hasDerivAt
  have hh : b ≤ (385:ℝ)/1000 := hb
  linarith [hr'.2]

theorem lowPrimitive_capReplacement_before {lam c r : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : c ≤ tEnd) (hr : r ∈ Icc ell c) :
    lowPrimitive lam (capReplacement lam d c) r = cap lam d.S r := by
  have hi : (∫ u in ell..r,(capReplacement lam d c).phi u) = ∫ u in ell..r,capScore lam d.S u := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc ell r := by simpa only [uIcc_of_le hr.1] using hu
    exact piecewise_eq_of_mem (Iic c) _ _ (show u ∈ Iic c from hu'.2.trans hr.2)
  change cap lam d.S ell+_ = _
  rw [hi,integral_capScore hd le_rfl hr.1 (hr.2.trans hc)]
  ring

theorem lowPrimitive_capReplacement_after {lam c r : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : c ∈ Icc ell tEnd)
    (hcontact : lowPrimitive lam d c = cap lam d.S c) (hr : r ∈ Icc c tEnd) :
    lowPrimitive lam (capReplacement lam d c) r = lowPrimitive lam d r := by
  have hleft := lowPrimitive_capReplacement_before hd hc.2 (show c ∈ Icc ell c from ⟨hc.1,le_rfl⟩)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (replacement_intervalIntegrable (c:=c) hd le_rfl hc.1 hc.2)
    (replacement_intervalIntegrable (c:=c) hd hc.1 hr.1 hr.2)
  have hi : (∫ u in c..r,(capReplacement lam d c).phi u) = ∫ u in c..r,d.phi u := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hr.1]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact piecewise_eq_of_notMem (Iic c) _ _ (show u ∉ Iic c from not_le.mpr hu.1)
  have hold := hd.lowPrimitive_sub hc ⟨hc.1.trans hr.1,hr.2⟩
  change cap lam d.S ell+(∫ u in ell..c,(capReplacement lam d c).phi u) = cap lam d.S c at hleft
  change cap lam d.S ell+(∫ u in ell..r,(capReplacement lam d c).phi u) = lowPrimitive lam d r
  rw [← hadd,hi]
  rw [hcontact] at hold
  linarith

/-- This is the low-rank portion of B.3 Step 2. It does not assume or claim
that the high-rank ODE is improved by the replacement. -/
theorem capReplacement_admissible {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : c ∈ Ioc ell tEnd)
    (hcontact : lowPrimitive lam d c = cap lam d.S c) :
    Admissible lam (capReplacement lam d c) := by
  have hc' : c ∈ Icc ell tEnd := ⟨hc.1.le,hc.2⟩
  refine ⟨hd.1,hd.2.1,hd.capReplacement_memLp,?_,?_,?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Icc,hd.2.2.2.1] with r hr hphi
    by_cases hrc : r ≤ c
    · change 0 ≤ (Iic c).piecewise (capScore lam d.S) d.phi r ∧ _
      change 0 ≤ (Iic c).piecewise (capScore lam d.S) d.phi r ∧ (Iic c).piecewise (capScore lam d.S) d.phi r ≤ lam-r
      rw [piecewise_eq_of_mem (Iic c) _ _ (show r ∈ Iic c from hrc)]
      exact ⟨(hd.capScore_bounds_before_contact hc hcontact r ⟨hr.1,hrc⟩).1.le,
        (hd.capScore_bounds_before_contact hc hcontact r ⟨hr.1,hrc⟩).2⟩
    · simpa only [capReplacement,piecewise_eq_of_notMem (Iic c) _ _ (show r ∉ Iic c from hrc)] using hphi
  · rw [lowPrimitive_capReplacement_after hd hc' hcontact ⟨hc.2,le_rfl⟩]
    exact hd.2.2.2.2.1
  · intro r hr
    by_cases hrc : r ≤ c
    · exact (lowPrimitive_capReplacement_before hd hc.2 ⟨hr.1,hrc⟩).le
    · rw [lowPrimitive_capReplacement_after hd hc' hcontact ⟨(lt_of_not_ge hrc).le,hr.2⟩]
      exact hd.lowPrimitive_le_cap hr

theorem lowPrimitive_le_capReplacement {lam c r : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : c ∈ Icc ell tEnd)
    (hcontact : lowPrimitive lam d c = cap lam d.S c) (hr : r ∈ Icc ell tEnd) :
    lowPrimitive lam d r ≤ lowPrimitive lam (capReplacement lam d c) r := by
  by_cases hrc : r ≤ c
  · rw [lowPrimitive_capReplacement_before hd hc.2 ⟨hr.1,hrc⟩]
    exact hd.lowPrimitive_le_cap hr
  · rw [lowPrimitive_capReplacement_after hd hc hcontact ⟨(lt_of_not_ge hrc).le,hr.2⟩]

end OptimalG.Variational
