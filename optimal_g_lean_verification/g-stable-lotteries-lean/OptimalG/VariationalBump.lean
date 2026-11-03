import OptimalG.SlaterPerturbation
import OptimalG.VariationalNormLimit

/-! Actual admissible local score bumps with compensating scalar slack. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

noncomputable def bumpMass (h : ℝ → ℝ) : ℝ := ∫ r in ell..tEnd, h r
noncomputable def bumpScalar (lam : ℝ) : ℝ := 1-lam/(1-ell)
noncomputable def bumpShift (lam : ℝ) (h : ℝ → ℝ) (t : ℝ) : ℝ := t*bumpMass h/bumpScalar lam
noncomputable def bumpData (lam : ℝ) (d : LowRankData) (h : ℝ → ℝ) (t : ℝ) : LowRankData :=
  ⟨d.S-bumpShift lam h t, fun r => d.phi r+t*h r⟩

theorem bumpScalar_pos {lam : ℝ} (hl : lam ∈ Icc lambdaLo lambdaHi) : 0 < bumpScalar lam := by
  unfold bumpScalar ell
  have hh := hl.2
  norm_num [lambdaHi] at hh ⊢
  linarith

theorem cap_slack_decrease (lam S q r : ℝ) : cap lam (S-q) r = cap lam S r+lam*q/(1-r) := by
  unfold cap
  ring

private theorem bump_intervalIntegrable {h : ℝ → ℝ}
    (hh : MemLp h ⊤ (volume.restrict (Icc ell tEnd))) {a b : ℝ}
    (ha : ell ≤ a) (hab : a ≤ b) (hb : b ≤ tEnd) : IntervalIntegrable h volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  have hi : IntegrableOn h (Icc ell tEnd) := MemLp.integrable (by simp) hh
  apply hi.mono_set
  exact Icc_subset_Icc ha hb

theorem lowPrimitive_bumpData {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    {h : ℝ → ℝ} (hh : MemLp h ⊤ (volume.restrict (Icc ell tEnd))) (t : ℝ)
    {r : ℝ} (hr : r ∈ Icc ell tEnd) :
    lowPrimitive lam (bumpData lam d h t) r =
      lowPrimitive lam d r+lam*bumpShift lam h t/(1-ell)+t*(∫ s in ell..r,h s) := by
  unfold lowPrimitive bumpData
  dsimp only
  rw [cap_slack_decrease, intervalIntegral.integral_add
    (hd.intervalIntegrable le_rfl hr.1 hr.2)
    ((bump_intervalIntegrable hh le_rfl hr.1 hr.2).const_mul t), intervalIntegral.integral_const_mul]
  ring

theorem bumpData_endpoint {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    {h : ℝ → ℝ} (hh : MemLp h ⊤ (volume.restrict (Icc ell tEnd))) (t : ℝ) :
    lowPrimitive lam (bumpData lam d h t) tEnd = quadratic lam tEnd-(bumpData lam d h t).S := by
  rw [lowPrimitive_bumpData hd hh t (by norm_num [ell, tEnd]), hd.2.2.2.2.1]
  have heq : bumpScalar lam*bumpShift lam h t = t*bumpMass h := by
    unfold bumpShift
    field_simp [(bumpScalar_pos hd.1).ne']
  change _ = quadratic lam tEnd-(d.S-bumpShift lam h t)
  change _ + t*bumpMass h = _
  unfold bumpScalar at heq
  ring_nf at heq ⊢
  linarith

theorem bump_partial_bounds {h : ℝ → ℝ}
    (hh : MemLp h ⊤ (volume.restrict (Icc ell tEnd)))
    (hh0 : ∀ᵐ r ∂volume.restrict (Icc ell tEnd), 0 ≤ h r)
    {r : ℝ} (hr : r ∈ Icc ell tEnd) :
    0 ≤ (∫ s in ell..r,h s) ∧ (∫ s in ell..r,h s) ≤ bumpMass h := by
  have h0 : ∀ᵐ s ∂volume, s ∈ Icc ell tEnd → 0 ≤ h s :=
    (ae_restrict_iff' measurableSet_Icc).mp hh0
  have hleft : 0 ≤ ∫ s in ell..r,h s := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hr.1
    change ∀ᵐ s ∂volume.restrict (Icc ell r), 0 ≤ h s
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [h0] with s hs
    intro hsr
    exact hs ⟨hsr.1, hsr.2.trans hr.2⟩
  have hright : 0 ≤ ∫ s in r..tEnd,h s := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hr.2
    change ∀ᵐ s ∂volume.restrict (Icc r tEnd), 0 ≤ h s
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [h0] with s hs
    intro hsr
    exact hs ⟨hr.1.trans hsr.1, hsr.2⟩
  have heq := intervalIntegral.integral_add_adjacent_intervals
    (bump_intervalIntegrable hh le_rfl hr.1 hr.2) (bump_intervalIntegrable hh hr.1 hr.2 le_rfl)
  exact ⟨hleft, by unfold bumpMass; linarith⟩

/-- A bounded bump supported strictly after a cap contact preserves all low
constraints when it fits inside the score and cap margins. -/
theorem bumpData_admissible {lam a m eta t : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {h : ℝ → ℝ}
    (hh : MemLp h ⊤ (volume.restrict (Icc ell tEnd)))
    (hb : ∀ᵐ r ∂volume.restrict (Icc ell tEnd), 0 ≤ h r ∧ h r ≤ 1)
    (hzero : ∀ r ≤ a, h r = 0)
    (hscore : ∀ᵐ r ∂volume.restrict (Icc ell tEnd), h r ≠ 0 → d.phi r ≤ lam-r-eta)
    (hcap : ∀ r ∈ Icc a tEnd, lowPrimitive lam d r+m ≤ cap lam d.S r)
    (ht : 0 ≤ t) (hteta : t ≤ eta) (htmass : t*bumpMass h ≤ m) :
    Admissible lam (bumpData lam d h t) := by
  have hmass : 0 ≤ bumpMass h :=
    (bump_partial_bounds hh (hb.mono fun _ h => h.1) (by norm_num [ell, tEnd])).1
  have hq : 0 ≤ bumpShift lam h t := div_nonneg (mul_nonneg ht hmass) (bumpScalar_pos hd.1).le
  have hlam0 : 0 ≤ lam := by have hh := hd.1.1; norm_num [lambdaLo] at hh; linarith
  refine ⟨hd.1, ?_, ?_, ?_, bumpData_endpoint hd hh t, ?_⟩
  · change d.S-bumpShift lam h t ≤ slackUpper lam
    linarith [hd.2.1]
  · exact hd.2.2.1.add (hh.const_mul t)
  · filter_upwards [hb, hscore, hd.2.2.2.1] with r hbr hsr hdr
    change 0 ≤ d.phi r+t*h r ∧ d.phi r+t*h r ≤ lam-r
    refine ⟨add_nonneg hdr.1 (mul_nonneg ht hbr.1), ?_⟩
    by_cases hz : h r = 0
    · simpa only [hz, mul_zero, add_zero] using hdr.2
    · have hs := hsr hz
      have hm := mul_le_mul_of_nonneg_left hbr.2 ht
      nlinarith
  · intro r hr
    rw [lowPrimitive_bumpData hd hh t hr]
    change _ ≤ cap lam (d.S-bumpShift lam h t) r
    rw [cap_slack_decrease]
    have hr1 : 0 < 1-r := by have hh := hr.2; norm_num [tEnd] at hh; linarith
    have hleft : lam*bumpShift lam h t/(1-ell) ≤ lam*bumpShift lam h t/(1-r) :=
      div_le_div₀ (mul_nonneg hlam0 hq) le_rfl hr1 (by linarith [hr.1])
    by_cases hra : r ≤ a
    · have hz : (∫ s in ell..r,h s) = 0 := by
        calc
          _ = ∫ _s in ell..r, (0 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro s hs
            exact hzero s ((by simpa only [uIcc_of_le hr.1] using hs : s ∈ Icc ell r).2.trans hra)
          _ = 0 := by simp
      rw [hz, mul_zero, add_zero]
      linarith [hd.lowPrimitive_le_cap hr]
    · have hm := hcap r ⟨(lt_of_not_ge hra).le,hr.2⟩
      have hi := mul_le_mul_of_nonneg_left
        (bump_partial_bounds hh (hb.mono fun _ h => h.1) hr).2 ht
      linarith

end OptimalG.Variational
