import OptimalG.VariationalCapContact

/-! Saturation outside the control ranks determines the actual primitive
on the entire terminal part of the low-rank interval. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter

 theorem minimizer_primitive_line_tail {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Ico ell xHi)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r=cap lam d.S r → r ≤ c) :
    ∀ r ∈ Icc xHi tEnd, lowPrimitive lam d r=quadratic lam r-d.S := by
  have hcx : xHi ≤ tEnd := by norm_num [xHi,tEnd]
  have hex : ell ≤ xHi := by norm_num [ell,xHi]
  have hsat := minimizer_saturates_outside_test_interval hd hl hmin hpass
    (show c ∈ Icc ell tEnd from ⟨hc.1,hc.2.le.trans hcx⟩) hlast
  have hne : ∀ᵐ r ∂volume, r ≠ xHi := by simp [ae_iff]
  have hline : d.phi =ᵐ[volume.restrict (Icc xHi tEnd)] (fun r => lam-r) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hne,
      ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hex le_rfl) hsat] with r hr hne hs
    have hxr : xHi < r := lt_of_le_of_ne hr.1 (Ne.symm hne)
    exact hs (hc.2.trans hxr) (fun hi => (not_le_of_gt hxr) hi.2)
  intro r hr
  have hi : (∫ t in r..tEnd,d.phi t)=quadratic lam tEnd-quadratic lam r := by
    rw [← integral_line]
    apply intervalIntegral.integral_congr_ae_restrict
    apply ae_restrict_of_ae_restrict_of_subset _ hline
    rw [uIoc_of_le hr.2]
    exact Ioc_subset_Icc_self.trans (Icc_subset_Icc hr.1 le_rfl)
  rw [← hd.lowPrimitive_sub ⟨hex.trans hr.1,hr.2⟩
    (show tEnd ∈ Icc ell tEnd by norm_num [ell,tEnd]),hd.2.2.2.2.1] at hi
  linarith

end OptimalG.Variational
