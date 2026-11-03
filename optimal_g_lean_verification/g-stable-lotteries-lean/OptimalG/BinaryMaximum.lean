import OptimalG.BinaryStationary

/-! Reduction of the two-class inequality to endpoints and stationary splits. -/
namespace OptimalG
open Set

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem binaryRatio_continuousOn {p b : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hb : 0 ≤ b) (hbp : b ≤ p) (hbl : b < lam) :
    ContinuousOn (binaryRatio phi lam p) (Icc 0 b) := by
  have ha : ContinuousOn (curvePrimitive phi) (Icc 0 b) :=
    h.primitive_continuous.mono (Icc_subset_Icc le_rfl (hbp.trans hp.2.le))
  have hc : ContinuousOn (fun q => curvePrimitive phi (q+1-p)) (Icc 0 b) := by
    apply h.primitive_continuous.comp (by fun_prop)
    intro q hq
    change 0 ≤ q+1-p ∧ q+1-p ≤ 1
    constructor <;> linarith [hq.1,hq.2,hp.2]
  exact (hc.sub ha).div (by fun_prop) (fun q hq =>
    sub_ne_zero.mpr (ne_of_gt (hq.2.trans_lt hbl)))

/-- Every interior maximizer is an actual stationary split. -/
theorem binaryRatio_bound_of_stationary {p b B : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hb : 0 ≤ b) (hbp : b ≤ p) (hbl : b < lam)
    (hzero : binaryRatio phi lam p 0 ≤ B) (hend : binaryRatio phi lam p b ≤ B)
    (hstationary : ∀ q ∈ Ioo (0 : ℝ) b,
      binaryStationaryNumerator phi lam p q=0 → binaryRatio phi lam p q ≤ B) :
    ∀ q ∈ Icc (0 : ℝ) b,binaryRatio phi lam p q ≤ B := by
  obtain ⟨r,hr,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hb)
    (h.binaryRatio_continuousOn hp hb hbp hbl)
  have hrB : binaryRatio phi lam p r ≤ B := by
    by_cases hr0 : r=0
    · simpa only [hr0] using hzero
    by_cases hrb : r=b
    · simpa only [hrb] using hend
    have hi : r ∈ Ioo (0 : ℝ) b := ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0),lt_of_le_of_ne hr.2 hrb⟩
    exact hstationary r hi (h.binaryRatio_stationary hp hi.1 (hi.2.trans_le hbp)
      (hi.2.trans hbl) (hm.isLocalMax (Icc_mem_nhds hi.1 hi.2)))
  intro q hq
  exact (hm hq).trans hrB

/-- For a mass below λ the right endpoint is automatically nonpositive. -/
theorem binaryRatio_at_mass {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hpl : p < lam) :
    binaryRatio phi lam p p ≤ 0 := by
  have hJ1 : curvePrimitive phi 1=0 := h.integral_zero
  have he : p+1-p=1 := by ring
  unfold binaryRatio
  rw [he,hJ1,zero_sub]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (h.primitive_pos hp).le)
    (sub_pos.mpr hpl).le

/-- A stationary-split certificate covers all low splits for masses below λ. -/
theorem binary_below_lam_of_stationary {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hpl : p < lam)
    (hzero : p*curvePrimitive phi (1-p) ≤ lam*curvePrimitive phi p)
    (hstationary : ∀ q ∈ Ioo (0 : ℝ) p,binaryStationaryNumerator phi lam p q=0 →
      binaryRatio phi lam p q ≤ curvePrimitive phi p/p) :
    ∀ q ∈ Icc (0 : ℝ) p,q+(p/curvePrimitive phi p)*packingDelta phi p q ≤ lam := by
  have hzero' : binaryRatio phi lam p 0 ≤ curvePrimitive phi p/p := by
    have hJ0 : curvePrimitive phi 0=0 := by simp [curvePrimitive]
    unfold binaryRatio
    simp only [zero_add,hJ0,sub_zero]
    exact (div_le_div_iff₀ h.lam_pos hp.1).mpr (by nlinarith only [hzero])
  have hall := h.binaryRatio_bound_of_stationary hp hp.1.le le_rfl hpl hzero'
    ((h.binaryRatio_at_mass hp hpl).trans (div_nonneg (h.primitive_pos hp).le hp.1.le)) hstationary
  intro q hq
  have hh := (div_le_div_iff₀ (sub_pos.mpr (hq.2.trans_lt hpl)) hp.1).mp (hall q hq)
  have he : 1-p+q=q+1-p := by ring
  have htest : (p/curvePrimitive phi p)*packingDelta phi p q ≤ lam-q := by
    unfold packingDelta
    rw [he,div_mul_eq_mul_div]
    exact (div_le_iff₀ (h.primitive_pos hp)).mpr (by nlinarith only [hh])
  linarith

end VerifierCurve
end OptimalG
