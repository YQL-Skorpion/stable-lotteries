import OptimalG.VerifierConditions
import OptimalG.WeightedLow

/-! Averaging the individual potentials, and checking the actual offset of each voter. -/
namespace OptimalG
open Set

noncomputable def averagedRankPotential {V : Type*} [Fintype V]
    (w s : V → ℝ) (phi : ℝ → ℝ) (lam z : ℝ) : ℝ :=
  weightedLow w (fun v => s v < lam) (fun v => phi (s v))
    (fun v => rankPotential phi lam (s v) z)

noncomputable def averagedCorrection {V : Type*} [Fintype V]
    (w s : V → ℝ) (phi : ℝ → ℝ) (lam : ℝ) (corr : ℝ → ℝ → ℝ) (p : ℝ) : ℝ :=
  lowExpectation w (fun v => s v < lam) (fun v => corr p (s v)) /
    lowExpectation w (fun v => s v < lam) (fun v => phi (s v))

section Average
variable {V : Type*} [Fintype V] (w s : V → ℝ) {phi : ℝ → ℝ} {lam : ℝ}
    (h : VerifierCurve phi lam) (hw : ∀ v, 0 ≤ w v) (hs : ∀ v, s v ∈ Icc (0 : ℝ) 1)
    (hA : 0 < lowExpectation w (fun v => s v < lam) (fun v => phi (s v)))
include h hw hs hA

theorem averagedRankPotential_nonneg {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ averagedRankPotential w s phi lam z := by
  have hh := weightedLow_mono w (fun v => s v < lam) (fun v => phi (s v))
    (fun _ => 0) (fun v => rankPotential phi lam (s v) z) hw
    (fun v hv => (h.positive ⟨(hs v).1, hv⟩).le) hA
    (fun v hv => h.potential_nonneg ⟨(hs v).1, hv⟩ hz)
  rwa [weightedLow_const _ _ _ 0 (ne_of_gt hA)] at hh

theorem averagedRankPotential_monotone :
    MonotoneOn (averagedRankPotential w s phi lam) (Icc 0 1) := by
  intro y hy z hz hyz
  apply weightedLow_mono _ _ _ _ _ hw
    (fun v hv => (h.positive ⟨(hs v).1, hv⟩).le) hA
  intro v hv
  exact h.potential_monotone ⟨(hs v).1, hv⟩ hy hz hyz

omit h hw hs in
theorem averagedRankPotential_low {z : ℝ} (hz : z ≤ lam) :
    averagedRankPotential w s phi lam z = 0 := by
  unfold averagedRankPotential
  simp only [rankPotential_low phi lam _ z hz]
  exact weightedLow_const _ _ _ 0 (ne_of_gt hA)

theorem averagedVerifier_first (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Icc 0 1) phi lam beta corr) {p q : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : 0 ≤ q) (hqp : q ≤ p) :
    q + beta p * packingDelta phi p q + averagedRankPotential w s phi lam q - lam ≤
      max (-phi q) 0 * averagedCorrection w s phi lam corr p := by
  have hh := weightedLow_mono w (fun v => s v < lam) (fun v => phi (s v))
    (fun v => q + beta p * packingDelta phi p q + rankPotential phi lam (s v) q - lam)
    (fun v => max (-phi q) 0 * (corr p (s v) / phi (s v))) hw
    (fun v hv => (h.positive ⟨(hs v).1, hv⟩).le) hA (by
      intro v hl
      have hpv := h.positive ⟨(hs v).1, hl⟩
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hpv).mpr
      simpa only [mul_div_assoc, mul_comm (phi (s v))] using
        hv.high_first p hp (s v) ⟨(hs v).1, hl⟩ q hq hqp)
  simp only [weightedLow_sub, weightedLow_add,
    weightedLow_const _ _ _ _ (ne_of_gt hA), weightedLow_smul,
    weightedLow_div_score _ _ _ _ (fun v hl => ne_of_gt (h.positive ⟨(hs v).1, hl⟩))] at hh
  exact hh

theorem averagedVerifier_second (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Icc 0 1) phi lam beta corr) {p q z : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : 0 ≤ q) (hqp : q ≤ p) (hpz : p ≤ z) (hz : z ≤ 1) :
    q + beta p * packingK phi p q z + averagedRankPotential w s phi lam q -
      averagedRankPotential w s phi lam z ≤
      max (-phi z) 0 * averagedCorrection w s phi lam corr p := by
  have hh := weightedLow_mono w (fun v => s v < lam) (fun v => phi (s v))
    (fun v => q + beta p * packingK phi p q z + rankPotential phi lam (s v) q -
      rankPotential phi lam (s v) z)
    (fun v => max (-phi z) 0 * (corr p (s v) / phi (s v))) hw
    (fun v hl => (h.positive ⟨(hs v).1, hl⟩).le) hA (by
      intro v hl
      have hpv := h.positive ⟨(hs v).1, hl⟩
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hpv).mpr
      simpa only [mul_div_assoc, mul_comm (phi (s v))] using
        hv.high_second p hp (s v) ⟨(hs v).1, hl⟩ q z hq hqp hpz hz)
  simp only [weightedLow_sub, weightedLow_add,
    weightedLow_const _ _ _ _ (ne_of_gt hA), weightedLow_smul,
    weightedLow_div_score _ _ _ _ (fun v hl => ne_of_gt (h.positive ⟨(hs v).1, hl⟩))] at hh
  exact hh

/-- First inequality of 5.2 for an actual packed slice. -/
theorem offset_first (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Icc 0 1) phi lam beta corr)
    (v : V) (p q k : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (hq : 0 ≤ q) (hqp : q ≤ p) (hqs : q ≤ s v) (hk : k ≤ packingDelta phi p q) :
    q + beta p * k + sliceCorrection w (fun u => s u < lam)
      (fun u => phi (s u)) (fun u => corr p (s u)) v ≤
      lam - averagedRankPotential w s phi lam q := by
  have hbk := mul_le_mul_of_nonneg_left hk (hv.beta_nonneg p hp)
  by_cases hl : s v < lam
  · have hh := hv.low_first p hp (s v) ⟨(hs v).1, hl⟩ q hq hqp hqs
    rw [sliceCorrection, if_pos hl,
      averagedRankPotential_low w s hA (hqs.trans hl.le)]
    linarith
  · have hsHigh : s v ∈ Icc lam 1 := ⟨le_of_not_gt hl, (hs v).2⟩
    have hc := correction_coefficient_nonneg w (fun u => s u < lam)
      (fun u => phi (s u)) (fun u => corr p (s u)) hw
      (fun u hu => hv.corr_nonneg p hp (s u) ⟨(hs u).1, hu⟩) hA
    have hbound := averagedVerifier_first w s h hw hs hA beta corr hv hp hq hqp
    have hneg := mul_le_mul_of_nonneg_right
      (h.negative_part_le ⟨hq, hqp.trans hp.2⟩ hsHigh hqs) hc
    rw [sliceCorrection, if_neg hl]
    change q + beta p * k + phi (s v) * averagedCorrection w s phi lam corr p ≤ _
    change max (-phi q) 0 * averagedCorrection w s phi lam corr p ≤
      -phi (s v) * averagedCorrection w s phi lam corr p at hneg
    nlinarith

/-- Second inequality of 5.2; the low case packs directly against s_v. -/
theorem offset_second (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Icc 0 1) phi lam beta corr)
    (v : V) (p q z k : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (hq : 0 ≤ q) (hqp : q ≤ p) (hpz : p ≤ z) (hzs : z ≤ s v)
    (hkz : k ≤ packingK phi p q z) (hks : k ≤ packingK phi p q (s v)) :
    q + beta p * k + sliceCorrection w (fun u => s u < lam)
      (fun u => phi (s u)) (fun u => corr p (s u)) v ≤
      averagedRankPotential w s phi lam z - averagedRankPotential w s phi lam q := by
  by_cases hl : s v < lam
  · have hh := hv.low_second p hp (s v) ⟨(hs v).1, hl⟩ q hq hqp (hpz.trans hzs)
    have hbk := mul_le_mul_of_nonneg_left hks (hv.beta_nonneg p hp)
    rw [sliceCorrection, if_pos hl,
      averagedRankPotential_low w s hA (hzs.trans hl.le),
      averagedRankPotential_low w s hA (hqp.trans (hpz.trans (hzs.trans hl.le)))]
    linarith
  · have hsHigh : s v ∈ Icc lam 1 := ⟨le_of_not_gt hl, (hs v).2⟩
    have hc := correction_coefficient_nonneg w (fun u => s u < lam)
      (fun u => phi (s u)) (fun u => corr p (s u)) hw
      (fun u hu => hv.corr_nonneg p hp (s u) ⟨(hs u).1, hu⟩) hA
    have hbound := averagedVerifier_second w s h hw hs hA beta corr hv hp hq hqp hpz (hzs.trans (hs v).2)
    have hneg := mul_le_mul_of_nonneg_right
      (h.negative_part_le ⟨hp.1.trans hpz, hzs.trans (hs v).2⟩ hsHigh hzs) hc
    have hbk := mul_le_mul_of_nonneg_left hkz (hv.beta_nonneg p hp)
    rw [sliceCorrection, if_neg hl]
    change q + beta p * k + phi (s v) * averagedCorrection w s phi lam corr p ≤ _
    change max (-phi z) 0 * averagedCorrection w s phi lam corr p ≤
      -phi (s v) * averagedCorrection w s phi lam corr p at hneg
    nlinarith

end Average
end OptimalG
