import OptimalG.BinaryMaximum

/-! The ratio's apparent singularity at λ does not leave a split unchecked:
the numerator is strictly negative there for every interior mass p≥λ. -/
namespace OptimalG
open Set

private theorem exists_left_negative {f : ℝ → ℝ} {p c q : ℝ}
    (hf : ContinuousOn f (Icc 0 p)) (hq : 0 ≤ q) (hqc : q < c) (hcp : c ≤ p)
    (hfc : f c < 0) : ∃ b, q < b ∧ b < c ∧ f b < 0 := by
  obtain ⟨δ,hδ,hnear⟩ := Metric.continuousWithinAt_iff.mp
    (hf c ⟨hq.trans hqc.le,hcp⟩) (-f c) (neg_pos.mpr hfc)
  let d := min (c-q) δ/2
  have hd : 0 < d := by dsimp [d]; exact div_pos (lt_min (sub_pos.mpr hqc) hδ) (by norm_num)
  have hdq : d < c-q := by dsimp [d]; linarith [min_le_left (c-q) δ]
  have hdδ : d < δ := by dsimp [d]; linarith [min_le_right (c-q) δ]
  refine ⟨c-d,by linarith,by linarith,?_⟩
  have hn := hnear (x := c-d) ⟨by linarith,by linarith⟩ (by
    rw [Real.dist_eq,abs_of_nonpos (show c-d-c ≤ 0 by linarith)]
    linarith)
  rw [Real.dist_eq] at hn
  linarith [(abs_lt.mp hn).2]

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem binary_numerator_continuousOn {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun q => curvePrimitive phi (q+1-p)-curvePrimitive phi q) (Icc 0 p) := by
  have hc : ContinuousOn (fun q => curvePrimitive phi (q+1-p)) (Icc 0 p) := by
    apply h.primitive_continuous.comp (by fun_prop)
    intro q hq
    change 0 ≤ q+1-p ∧ q+1-p ≤ 1
    constructor <;> linarith [hq.1,hq.2,hp.2]
  exact hc.sub (h.primitive_continuous.mono (Icc_subset_Icc le_rfl hp.2.le))

theorem binary_numerator_at_lam_neg {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hlp : lam ≤ p) :
    curvePrimitive phi (lam+1-p)-curvePrimitive phi lam < 0 := by
  let m := lam+(1-p)/2
  have hlm : lam < m := by dsimp [m]; linarith [hp.2]
  have hmr : m < lam+1-p := by dsimp [m]; linarith [hp.2]
  have hr1 : lam+1-p ≤ 1 := by linarith
  have hm0 : 0 ≤ m := h.lam_pos.le.trans hlm.le
  have hphi : phi m < 0 := by
    have hh := h.decreasing h.lam_mem ⟨hm0,hmr.le.trans hr1⟩ hlm
    simpa only [h.at_lam] using hh
  have hleft := h.primitive_increment_upper h.lam_pos.le hlm.le (hmr.le.trans hr1)
  rw [h.at_lam,mul_zero] at hleft
  have hright := h.primitive_increment_upper hm0 hmr.le hr1
  have hneg := mul_neg_of_pos_of_neg (sub_pos.mpr hmr) hphi
  linarith

/-- A finite compact interval covers any specified split before λ. -/
theorem binaryRatio_negative_cut {p q : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hlp : lam ≤ p) (hq : 0 ≤ q) (hql : q < lam) :
    ∃ b,q < b ∧ b < lam ∧ binaryRatio phi lam p b < 0 := by
  obtain ⟨b,hqb,hbl,hn⟩ := exists_left_negative (h.binary_numerator_continuousOn hp)
    hq hql hlp (h.binary_numerator_at_lam_neg hp hlp)
  exact ⟨b,hqb,hbl,div_neg_of_neg_of_pos hn (sub_pos.mpr hbl)⟩

/-- Endpoints and stationary points suffice also when the mass reaches or exceeds λ. -/
theorem binary_above_lam_of_stationary {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hlp : lam ≤ p)
    (hzero : p*curvePrimitive phi (1-p) ≤ lam*curvePrimitive phi p)
    (hstationary : ∀ q ∈ Ioo (0 : ℝ) lam,binaryStationaryNumerator phi lam p q=0 →
      binaryRatio phi lam p q ≤ curvePrimitive phi p/p) :
    ∀ q ∈ Icc (0 : ℝ) lam,q+(p/curvePrimitive phi p)*packingDelta phi p q ≤ lam := by
  have hzero' : binaryRatio phi lam p 0 ≤ curvePrimitive phi p/p := by
    have hJ0 : curvePrimitive phi 0=0 := by simp [curvePrimitive]
    unfold binaryRatio
    simp only [zero_add,hJ0,sub_zero]
    exact (div_le_div_iff₀ h.lam_pos hp.1).mpr (by nlinarith only [hzero])
  intro q hq
  rcases eq_or_lt_of_le hq.2 with he | hql
  · subst q
    have hd : packingDelta phi p lam ≤ 0 := by
      have he : 1-p+lam=lam+1-p := by ring
      simpa only [packingDelta,he] using (h.binary_numerator_at_lam_neg hp hlp).le
    have hm := mul_nonpos_of_nonneg_of_nonpos (div_pos hp.1 (h.primitive_pos hp)).le hd
    linarith
  · obtain ⟨b,hqb,hbl,hneg⟩ := h.binaryRatio_negative_cut hp hlp hq.1 hql
    have hall := h.binaryRatio_bound_of_stationary hp (hq.1.trans hqb.le) (hbl.le.trans hlp) hbl hzero'
      (hneg.le.trans (div_nonneg (h.primitive_pos hp).le hp.1.le))
      (fun r hr => hstationary r ⟨hr.1,hr.2.trans hbl⟩)
    have hh := (div_le_div_iff₀ (sub_pos.mpr hql) hp.1).mp (hall q ⟨hq.1,hqb.le⟩)
    have he : 1-p+q=q+1-p := by ring
    have ht : (p/curvePrimitive phi p)*packingDelta phi p q ≤ lam-q := by
      unfold packingDelta
      rw [he,div_mul_eq_mul_div]
      exact (div_le_iff₀ (h.primitive_pos hp)).mpr (by nlinarith only [hh])
    linarith

end VerifierCurve
end OptimalG
