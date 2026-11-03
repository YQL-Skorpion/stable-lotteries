import OptimalG.VariationalBumpControl
import OptimalG.VariationalUniformControl

/-!
# Excluding positive inactive bumps

This is the variational core of Lemma B.1. A positive bump with score and cap
slack cannot avoid all nearly active controls at an interior minimum. The proof
uses exact finite perturbations and scalar comparison, with no differentiated
maximization or adjoint assumptions.
-/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

 theorem no_inactive_positive_bump {lam a m eta δ : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    {h : ℝ → ℝ} (hh : MemLp h ⊤ (volume.restrict (Icc ell tEnd)))
    (hb : ∀ᵐ r ∂volume.restrict (Icc ell tEnd), 0 ≤ h r ∧ h r ≤ 1)
    (hmass : 0 < bumpMass h) (hzero : ∀ r ≤ a, h r = 0)
    (heta : 0 < eta)
    (hscore : ∀ᵐ r ∂volume.restrict (Icc ell tEnd), h r ≠ 0 → d.phi r ≤ lam-r-eta)
    (hm : 0 < m) (hcap : ∀ r ∈ Icc a tEnd, lowPrimitive lam d r+m ≤ cap lam d.S r)
    (hδ : 0 < δ)
    (hinactive : ∀ z ∈ Icc zStart zEnd, ∀ᵐ c ∂controlMeasure,
      (h c.2.1 ≠ 0 ∨ h c.2.2 ≠ 0) →
        vectorField lam d z (continuation lam d z)+δ ≤ controlH lam d z (continuation lam d z) c) :
    False := by
  let tmax := min eta (m/bumpMass h)
  have htmax : 0 < tmax := lt_min heta (div_pos hm hmass)
  obtain ⟨tn, _, htn, ht⟩ := exists_seq_strictAnti_tendsto' htmax
  let dn := fun n => bumpData lam d h (tn n)
  let qn := fun n => bumpShift lam h (tn n)
  have hn (n : ℕ) : Admissible lam (dn n) := by
    apply bumpData_admissible hd hh hb hzero hscore hcap (htn n).1.le
    · exact (htn n).2.le.trans (min_le_left _ _)
    · have hsmall := (htn n).2.le.trans (min_le_right eta (m/bumpMass h))
      exact (le_div_iff₀ hmass).mp hsmall
  have hq : Tendsto qn atTop (𝓝 0) := by
    change Tendsto (fun n => tn n*bumpMass h/bumpScalar lam) atTop (𝓝 0)
    simpa only [zero_mul, zero_div] using (ht.mul_const (bumpMass h)).div_const (bumpScalar lam)
  have hqp (n : ℕ) : 0 < qn n := div_pos (mul_pos (htn n).1 hmass) (bumpScalar_pos hd.1)
  have hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S) := by
    change Tendsto (fun n => d.S-qn n) atTop (𝓝 d.S)
    simpa only [sub_zero] using (tendsto_const_nhds (x := d.S)).sub hq
  have hhb : EssentiallyBounded h (volume.restrict (Icc ell tEnd)) := by
    refine ⟨1, ?_⟩
    filter_upwards [hb] with r hr
    rw [abs_of_nonneg hr.1]
    exact hr.2
  have hphi : AENormTendsto (fun n => (dn n).phi) d.phi (volume.restrict (Icc ell tEnd)) := by
    have hc := (BoundedAENormTendsto.scalar (I := ℝ) (μ := volume.restrict (Icc ell tEnd)) ht).mul
      (BoundedAENormTendsto.refl h hhb)
    change AENormTendsto (fun n r => d.phi r+tn n*h r) d.phi (volume.restrict (Icc ell tEnd))
    simpa only [zero_mul, add_zero] using (AENormTendsto.refl d.phi).add hc.converges
  have hJ := lowPrimitive_tendstoUniformly_of_strong_data (fun _ => lam) dn hn hd
    tendsto_const_nhds hS hphi
  obtain ⟨en, he, hen⟩ := controlH_uniform_path_error (fun _ => lam) dn hn hd
    tendsto_const_nhds hS hJ hphi (continuation lam d) (continuation_continuous hd.isContinuation) qn hq
  let δ' := min δ (1/10000)
  have hδ' : 0 < δ' := lt_min hδ (by norm_num)
  obtain ⟨n, hsmall⟩ := ((tendsto_order.mp he).2 δ' hδ').exists
  have hfield : ∀ z ∈ Icc zStart zEnd,
      vectorField lam d z (continuation lam d z) ≤ vectorField lam (dn n) z (continuation lam d z+qn n) := by
    intro z hz
    apply le_min (vectorField_le_line lam d z (continuation lam d z))
    apply le_essInf_of_ae_le _ _ ((hn n).controlH_bounded z (continuation lam d z+qn n)).boundedAbove.isCoboundedUnder_ge
    have hceil := ae_control_lowRanks _ hd.2.2.2.1
    filter_upwards [(hen n).2, ae_restrict_mem controlDomain_measurable, hceil,
      hinactive z hz, ae_essInf_le (hd.controlH_bounded z (continuation lam d z)).boundedBelow]
      with c herr hc hphiC hgap hlower
    have hlow : vectorField lam d z (continuation lam d z) ≤ controlH lam d z (continuation lam d z) c :=
      (min_le_right _ _).trans hlower
    by_cases hnear : controlH lam d z (continuation lam d z) c <
        vectorField lam d z (continuation lam d z)+δ'
    · have hunchanged : h c.2.1 = 0 ∧ h c.2.2 = 0 := by
        constructor
        · by_contra hhx
          have hgg := hgap (Or.inl hhx)
          have hδle : δ' ≤ δ := min_le_left _ _
          linarith
        · by_contra hhy
          have hgg := hgap (Or.inr hhy)
          have hδle : δ' ≤ δ := min_le_left _ _
          linarith
      apply hlow.trans
      apply hd.bump_control_nondecreasing hh (hb.mono fun _ h => h.1) (htn n).1.le
        (hn n) hc hz _ (hd.continuation_le_quadratic hd.isContinuation z hz)
        hphiC.1.2 hphiC.2.2 _ hunchanged.1 hunchanged.2
      · have hroot := hd.continuation_above_root_budget hd.isContinuation hpass hz
        linarith
      · have hline := vectorField_le_line lam d z (continuation lam d z)
        have hδle : δ' ≤ 1/10000 := min_le_right _ _
        linarith
    · have hf := le_of_not_gt hnear
      have hec := herr z hz
      have hl := neg_abs_le (controlH lam (dn n) z (continuation lam d z+qn n) c-
        controlH lam d z (continuation lam d z) c)
      linarith
  exact no_slack_decrease_with_shifted_continuation hd (hn n) hl (hqp n) hmin hpass rfl
    ((hn n).continuation_shift_of_field_comparison rfl hfield hd)

end OptimalG.Variational
