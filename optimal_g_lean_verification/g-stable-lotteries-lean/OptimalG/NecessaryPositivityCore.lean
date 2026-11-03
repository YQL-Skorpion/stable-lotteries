import OptimalG.RunningEnvelope
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The interior-primitive positivity argument in Appendix A.2, without the
incorrect final assertion about the score at rank zero. -/
namespace OptimalG
open Set Filter
open scoped Topology

/-- A continuous function on a closed interval has a rightmost minimizer. -/
theorem exists_rightmost_minimum {J : ℝ → ℝ} (hJ : Continuous J) :
    ∃ q ∈ Icc (0 : ℝ) 1, (∀ r ∈ Icc (0 : ℝ) 1, J q ≤ J r) ∧
      ∀ r ∈ Icc (0 : ℝ) 1, J r = J q → r ≤ q := by
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) 1).Nonempty by exact ⟨0, by norm_num⟩) hJ.continuousOn
  let K : Set ℝ := Icc 0 1 ∩ J ⁻¹' {J a}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_singleton.preimage hJ)
  obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn
    (show K.Nonempty from ⟨a, ha, rfl⟩) continuousOn_id
  refine ⟨q, hq.1, ?_, ?_⟩
  · intro r hr
    have hqe : J q = J a := hq.2
    rw [hqe]
    exact hmin hr
  · intro r hr heq
    apply hmax
    exact ⟨hr, heq.trans hq.2⟩

/-- The positive-primitive version of the two-class test forces positivity at
every interior rank. No monotonicity or sign assumption on the score is used. -/
theorem primitive_positive_of_two_class
    {J phi : ℝ → ℝ} {lam : ℝ}
    (hJ : Continuous J) (hd : ∀ r, HasDerivAt J (phi r) r)
    (h0 : J 0 = 0) (h1 : J 1 = 0) (hphi1 : phi 1 ≤ -1)
    (hL0 : 0 < lam) (hL1 : lam < 1)
    (htail : ∀ r ∈ Ico lam 1, 0 < J r)
    (htest : ∀ p q : ℝ, p ∈ Ioo 0 1 → 0 ≤ q → q ≤ p → q ≤ lam →
      0 < J p → p * (J (1 - p + q) - J q) ≤ (lam - q) * J p) :
    ∀ r ∈ Ioo (0 : ℝ) 1, 0 < J r := by
  let K : Set ℝ := Icc 0 lam ∩ J ⁻¹' Iic 0
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_Iic.preimage hJ)
  obtain ⟨c, hc, hmax⟩ := hK.exists_isMaxOn
    (show K.Nonempty from ⟨0, ⟨le_rfl, hL0.le⟩, by simpa [h0]⟩) continuousOn_id
  have hc0 : 0 ≤ c := hc.1.1
  have hcL : c < lam := by
    have hle := hc.1.2
    by_contra! hn
    have heq : c = lam := le_antisymm hle hn
    have hh := htail lam ⟨le_rfl, hL1⟩
    have hcJ : J c ≤ 0 := hc.2
    rw [heq] at hcJ
    linarith
  have hc1 : c < 1 := hcL.trans hL1
  have hafter : ∀ p ∈ Ioo c 1, 0 < J p := by
    intro p hp
    by_cases hpL : p ≤ lam
    · by_contra! hn
      have hh : p ≤ c := hmax ⟨⟨hc0.trans hp.1.le, hpL⟩, hn⟩
      linarith [hp.1]
    · exact htail p ⟨(lt_of_not_ge hpL).le, hp.2⟩
  have hcJ : J c = 0 := by
    apply le_antisymm hc.2
    have hl : Tendsto J (𝓝[>] c) (𝓝 (J c)) := hJ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hl
    filter_upwards [Ioo_mem_nhdsGT hc1] with p hp
    exact (hafter p hp).le
  have hnonneg : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ J r := by
    by_contra! hn
    obtain ⟨r, hr, hrneg⟩ := hn
    obtain ⟨q, hq, hqmin, hqmax⟩ := exists_rightmost_minimum hJ
    have hqneg : J q < 0 := (hqmin r hr).trans_lt hrneg
    have hq0 : 0 < q := by
      by_contra! hn
      have heq : q = 0 := le_antisymm hn hq.1
      simpa [heq, h0] using hqneg
    have hq1 : q < 1 := by
      by_contra! hn
      have heq : q = 1 := le_antisymm hq.2 hn
      simpa [heq, h1] using hqneg
    have hqc : q < c := by
      have hqL : q ≤ lam := by
        by_contra! hn
        have hh := htail q ⟨hn.le, hq1⟩
        linarith
      have hle : q ≤ c := hmax ⟨⟨hq.1, hqL⟩, hqneg.le⟩
      exact lt_of_le_of_ne hle (by intro heq; rw [heq, hcJ] at hqneg; linarith)
    have hlim : c * (J (1 - c + q) - J q) ≤ (lam - q) * J c := by
      have hl : Tendsto (fun p : ℝ => p * (J (1 - p + q) - J q)) (𝓝[>] c)
          (𝓝 (c * (J (1 - c + q) - J q))) :=
        ((continuous_id.mul ((hJ.comp ((continuous_const.sub continuous_id).add continuous_const)).sub continuous_const)).tendsto c).mono_left nhdsWithin_le_nhds
      have hr : Tendsto (fun p : ℝ => (lam - q) * J p) (𝓝[>] c)
          (𝓝 ((lam - q) * J c)) :=
        ((continuous_const.mul hJ).tendsto c).mono_left nhdsWithin_le_nhds
      apply le_of_tendsto_of_tendsto hl hr
      filter_upwards [Ioo_mem_nhdsGT hc1] with p hp
      exact htest p q ⟨lt_of_le_of_lt hc0 hp.1, hp.2⟩ hq.1
        (hqc.le.trans hp.1.le) (hqc.le.trans hcL.le) (hafter p hp)
    rw [hcJ, mul_zero] at hlim
    have hcpos : 0 < c := hq0.trans hqc
    have hle : J (1 - c + q) ≤ J q := by nlinarith
    have hz : 1 - c + q ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have heq := le_antisymm hle (hqmin _ hz)
    have hh := hqmax _ hz heq
    linarith
  have hczero : c = 0 := by
    by_contra! hn
    have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hn)
    have hlocal : IsLocalMin J c := by
      filter_upwards [Icc_mem_nhds hcpos hc1] with r hr
      change J c ≤ J r
      rw [hcJ]
      exact hnonneg r hr
    have hphic : phi c = 0 := hlocal.hasDerivAt_eq_zero (hd c)
    let F : ℝ → ℝ := fun p => p * (J (1 - p + c) - J c) - (lam - c) * J p
    have hFd : HasDerivAt F (-c * phi 1) c := by
      have hi : HasDerivAt (fun p : ℝ => 1 - p + c) (-1) c := by
        convert ((hasDerivAt_id c).const_sub 1).add_const c using 1 <;> first | rfl | norm_num
      have hj := (hd (1 - c + c)).comp c (h := fun p : ℝ => 1 - p + c) hi
      have hh := ((hasDerivAt_id c).mul (hj.sub_const (J c))).sub ((hd c).const_mul (lam - c))
      convert hh using 1 <;> first | rfl | (simp [hphic, h1, hcJ] <;> ring)
    have hFzero : F c = 0 := by simp [F, h1, hcJ]
    have hderiv : -c * phi 1 ≤ 0 := by
      apply le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hFd).2
      filter_upwards [Ioo_mem_nhdsGT hc1] with p hp
      have hh := htest p c ⟨hcpos.trans hp.1, hp.2⟩ hc0 hp.1.le hcL.le (hafter p hp)
      have hFp : F p ≤ 0 := sub_nonpos.mpr hh
      rw [slope_def_field, hFzero, sub_zero]
      exact div_nonpos_of_nonpos_of_nonneg hFp (sub_nonneg.mpr hp.1.le)
    nlinarith
  intro r hr
  exact hafter r (by simpa [hczero] using hr)

end OptimalG
