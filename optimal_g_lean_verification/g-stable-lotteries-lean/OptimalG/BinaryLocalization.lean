import OptimalG.BinaryDerivativeReduction

/-! Actual maximizer localization for C.3. Monotonicity of the stationary
numerator is derived from finite score increments, without an everywhere
second derivative of the score. -/
namespace OptimalG
open Set

noncomputable def binaryScoreIncrement (phi : ℝ → ℝ) (p q : ℝ) : ℝ :=
  phi (q+1-p)-phi q

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

private theorem binaryNumerator_hasDerivAt {p q : ℝ} (hp : p ∈ Ioo (0:ℝ) 1)
    (hq : q ∈ Ioo (0:ℝ) p) :
    HasDerivAt (fun r => curvePrimitive phi (r+1-p)-curvePrimitive phi r)
      (binaryScoreIncrement phi p q) q := by
  have hr : q+1-p ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hq.1,hp.2],by linarith [hq.2]⟩
  convert! ((h.primitive_hasDerivAt hr).comp q
    (((hasDerivAt_id q).add_const 1).sub_const p)).sub
    (h.primitive_hasDerivAt ⟨hq.1,hq.2.trans hp.2⟩) using 1 <;>
    first | rfl | simp only [binaryScoreIncrement,mul_one]

/-- Increasing score increments give an increasing stationary numerator. -/
theorem binaryStationaryNumerator_monotone {p a b : ℝ}
    (hp : p ∈ Ioo (0:ℝ) 1) (ha : 0≤a) (hbp : b≤p) (hbl : b≤lam)
    (hd : MonotoneOn (binaryScoreIncrement phi p) (Icc a b)) :
    MonotoneOn (binaryStationaryNumerator phi lam p) (Icc a b) := by
  intro x hx y hy hxy
  have hcont := (h.binary_numerator_continuousOn hp).mono
    (Icc_subset_Icc (ha.trans hx.1) (hy.2.trans hbp))
  have hder (q : ℝ) (hq : q ∈ interior (Icc x y)) :=
    h.binaryNumerator_hasDerivAt hp
      (show q ∈ Ioo (0:ℝ) p by rw [interior_Icc] at hq; constructor <;> linarith [hx.1,hy.2,hq.1,hq.2])
  have hi := (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv hcont
    (fun q hq => (hder q hq).differentiableAt.differentiableWithinAt)
    (C:=binaryScoreIncrement phi p x) (by
      intro q hq
      rw [(hder q hq).deriv]
      rw [interior_Icc] at hq
      exact hd hx ⟨hx.1.trans hq.1.le,hq.2.le.trans hy.2⟩ hq.1.le)
    x ⟨le_rfl,hxy⟩ y ⟨hxy,le_rfl⟩ hxy
  have hm := mul_nonneg (sub_nonneg.mpr (hy.2.trans hbl)) (sub_nonneg.mpr (hd hx hy hxy))
  unfold binaryStationaryNumerator binaryScoreIncrement at *
  nlinarith only [hi,hm]

/-- Decreasing score increments give a decreasing stationary numerator. -/
theorem binaryStationaryNumerator_antitone {p a b : ℝ}
    (hp : p ∈ Ioo (0:ℝ) 1) (ha : 0≤a) (hbp : b≤p) (hbl : b≤lam)
    (hd : AntitoneOn (binaryScoreIncrement phi p) (Icc a b)) :
    AntitoneOn (binaryStationaryNumerator phi lam p) (Icc a b) := by
  intro x hx y hy hxy
  have hcont := (h.binary_numerator_continuousOn hp).mono
    (Icc_subset_Icc (ha.trans hx.1) (hy.2.trans hbp))
  have hder (q : ℝ) (hq : q ∈ interior (Icc x y)) :=
    h.binaryNumerator_hasDerivAt hp
      (show q ∈ Ioo (0:ℝ) p by rw [interior_Icc] at hq; constructor <;> linarith [hx.1,hy.2,hq.1,hq.2])
  have hi := (convex_Icc x y).image_sub_le_mul_sub_of_deriv_le hcont
    (fun q hq => (hder q hq).differentiableAt.differentiableWithinAt)
    (C:=binaryScoreIncrement phi p x) (by
      intro q hq
      rw [(hder q hq).deriv]
      rw [interior_Icc] at hq
      exact hd hx ⟨hx.1.trans hq.1.le,hq.2.le.trans hy.2⟩ hq.1.le)
    x ⟨le_rfl,hxy⟩ y ⟨hxy,le_rfl⟩ hxy
  have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hy.2.trans hbl))
    (sub_nonpos.mpr (hd hx hy hxy))
  unfold binaryStationaryNumerator binaryScoreIncrement at *
  nlinarith only [hi,hm]

theorem binaryRatio_monotone_of_numerator {p a b : ℝ}
    (hp : p ∈ Ioo (0:ℝ) 1) (ha : 0≤a) (hbp : b≤p) (hbl : b<lam)
    (hn : ∀ q ∈ Ioo a b,0≤binaryStationaryNumerator phi lam p q) :
    MonotoneOn (binaryRatio phi lam p) (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · by_cases hab : a≤b
    · exact (h.binaryRatio_continuousOn hp (ha.trans hab) hbp hbl).mono
        (Icc_subset_Icc ha le_rfl)
    · simp only [Icc_eq_empty_of_lt (lt_of_not_ge hab),continuousOn_empty]
  · intro q hq
    rw [interior_Icc] at hq
    exact (h.binaryRatio_hasDerivAt hp (ha.trans_lt hq.1) (hq.2.trans_le hbp)
      (hq.2.trans hbl)).differentiableAt.differentiableWithinAt
  · intro q hq
    rw [interior_Icc] at hq
    rw [(h.binaryRatio_hasDerivAt hp (ha.trans_lt hq.1) (hq.2.trans_le hbp) (hq.2.trans hbl)).deriv]
    exact div_nonneg (hn q hq) (sq_nonneg _)

theorem binaryRatio_antitone_of_numerator {p a b : ℝ}
    (hp : p ∈ Ioo (0:ℝ) 1) (ha : 0≤a) (hbp : b≤p) (hbl : b<lam)
    (hn : ∀ q ∈ Ioo a b,binaryStationaryNumerator phi lam p q≤0) :
    AntitoneOn (binaryRatio phi lam p) (Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · by_cases hab : a≤b
    · exact (h.binaryRatio_continuousOn hp (ha.trans hab) hbp hbl).mono
        (Icc_subset_Icc ha le_rfl)
    · simp only [Icc_eq_empty_of_lt (lt_of_not_ge hab),continuousOn_empty]
  · intro q hq
    rw [interior_Icc] at hq
    exact (h.binaryRatio_hasDerivAt hp (ha.trans_lt hq.1) (hq.2.trans_le hbp)
      (hq.2.trans hbl)).differentiableAt.differentiableWithinAt
  · intro q hq
    rw [interior_Icc] at hq
    rw [(h.binaryRatio_hasDerivAt hp (ha.trans_lt hq.1) (hq.2.trans_le hbp) (hq.2.trans hbl)).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (hn q hq) (sq_nonneg _)

/-- Where the stationary numerator increases, the ratio is bounded by its
endpoint values even if its derivative changes from negative to positive. -/
theorem binaryRatio_max_endpoints_of_numerator_monotone {p a b : ℝ}
    (hp : p ∈ Ioo (0:ℝ) 1) (ha : 0≤a) (hbp : b≤p) (hbl : b<lam)
    (hn : MonotoneOn (binaryStationaryNumerator phi lam p) (Icc a b)) :
    ∀ q ∈ Icc a b,binaryRatio phi lam p q≤max (binaryRatio phi lam p a) (binaryRatio phi lam p b) := by
  intro q hq
  by_cases hN : binaryStationaryNumerator phi lam p q≤0
  · have hm := h.binaryRatio_antitone_of_numerator hp ha (hq.2.trans hbp) (hq.2.trans_lt hbl)
      (fun r hr => (hn ⟨hr.1.le,hr.2.le.trans hq.2⟩ hq hr.2.le).trans hN)
    exact (hm ⟨le_rfl,hq.1⟩ ⟨hq.1,le_rfl⟩ hq.1).trans (le_max_left _ _)
  · have hm := h.binaryRatio_monotone_of_numerator hp (ha.trans hq.1) hbp hbl
      (fun r hr => (le_of_not_ge hN).trans (hn hq ⟨hq.1.trans hr.1.le,hr.2.le⟩ hr.1.le))
    exact (hm ⟨le_rfl,hq.2⟩ ⟨hq.2,le_rfl⟩ hq.2).trans (le_max_right _ _)

/-- An increasing-then-decreasing numerator with nonnegative final value
cannot produce a ratio maximum above its two endpoint values. -/
theorem binaryRatio_max_endpoints_of_numerator_unimodal {p a b c : ℝ}
    (hp : p ∈ Ioo (0:ℝ) 1) (ha : 0≤a) (hbp : b≤p) (hbl : b<lam)
    (hc : c ∈ Icc a b)
    (hup : MonotoneOn (binaryStationaryNumerator phi lam p) (Icc a c))
    (hdown : AntitoneOn (binaryStationaryNumerator phi lam p) (Icc c b))
    (hend : 0≤binaryStationaryNumerator phi lam p b) :
    ∀ q ∈ Icc a b,binaryRatio phi lam p q≤max (binaryRatio phi lam p a) (binaryRatio phi lam p b) := by
  have hm := h.binaryRatio_monotone_of_numerator hp (ha.trans hc.1) hbp hbl
    (fun r hr => hend.trans (hdown ⟨hr.1.le,hr.2.le⟩ ⟨hc.2,le_rfl⟩ hr.2.le))
  have hcb := hm ⟨le_rfl,hc.2⟩ ⟨hc.2,le_rfl⟩ hc.2
  intro q hq
  by_cases hqc : q≤c
  · exact (h.binaryRatio_max_endpoints_of_numerator_monotone hp ha (hc.2.trans hbp)
      (hc.2.trans_lt hbl) hup q ⟨hq.1,hqc⟩).trans (max_le_max_left _ hcb)
  · exact (hm ⟨le_of_not_ge hqc,hq.2⟩ ⟨hc.2,le_rfl⟩ hq.2).trans (le_max_right _ _)


/-- Finite score-slope separation controls the score increment without any
pointwise second derivative. -/
theorem binaryScoreIncrement_antitone_of_slopes {p a b slope : ℝ}
    (hlow : ∀ x ∈ Icc a b,∀ y ∈ Icc a b,x≤y → slope*(y-x)≤phi y-phi x)
    (hshift : ∀ x ∈ Icc a b,∀ y ∈ Icc a b,x≤y →
      phi (y+1-p)-phi (x+1-p)≤slope*(y-x)) :
    AntitoneOn (binaryScoreIncrement phi p) (Icc a b) := by
  intro x hx y hy hxy
  have h1 := hlow x hx y hy hxy
  have h2 := hshift x hx y hy hxy
  unfold binaryScoreIncrement
  linarith only [h1,h2]

theorem binaryScoreIncrement_monotone_of_slopes {p a b slope : ℝ}
    (hlow : ∀ x ∈ Icc a b,∀ y ∈ Icc a b,x≤y → phi y-phi x≤slope*(y-x))
    (hshift : ∀ x ∈ Icc a b,∀ y ∈ Icc a b,x≤y →
      slope*(y-x)≤phi (y+1-p)-phi (x+1-p)) :
    MonotoneOn (binaryScoreIncrement phi p) (Icc a b) := by
  intro x hx y hy hxy
  have h1 := hlow x hx y hy hxy
  have h2 := hshift x hx y hy hxy
  unfold binaryScoreIncrement
  linarith only [h1,h2]

/-- Any actual zero of a decreasing stationary numerator is a global ratio
maximizer on that rank band; neither uniqueness nor differentiability of the
maximizing rank as a function of mass is assumed. -/
theorem binaryRatio_le_stationary_root {p a r : ℝ}
    (hp : p ∈ Ioo (0:ℝ) 1) (ha : 0≤a) (hlp : lam≤p)
    (hr : r ∈ Ico a lam)
    (hn : AntitoneOn (binaryStationaryNumerator phi lam p) (Icc a lam))
    (hroot : binaryStationaryNumerator phi lam p r=0) :
    ∀ q ∈ Ico a lam,binaryRatio phi lam p q≤binaryRatio phi lam p r := by
  intro q hq
  by_cases hqr : q≤r
  · have hm := h.binaryRatio_monotone_of_numerator hp (ha.trans hq.1)
      (hr.2.le.trans hlp) hr.2 (fun t ht => by
        have hh := hn ⟨hq.1.trans ht.1.le,ht.2.le.trans hr.2.le⟩
          ⟨hr.1,hr.2.le⟩ ht.2.le
        simpa only [hroot] using hh)
    exact hm ⟨le_rfl,hqr⟩ ⟨hqr,le_rfl⟩ hqr
  · have hm := h.binaryRatio_antitone_of_numerator hp (ha.trans hr.1)
      (hq.2.le.trans hlp) hq.2 (fun t ht => by
        have hh := hn ⟨hr.1,hr.2.le⟩
          ⟨hr.1.trans ht.1.le,ht.2.le.trans hq.2.le⟩ ht.1.le
        simpa only [hroot] using hh)
    exact hm ⟨le_rfl,le_of_not_ge hqr⟩ ⟨le_of_not_ge hqr,le_rfl⟩ (le_of_not_ge hqr)

/-- This is the analytic maximizer-coverage step used by both the affine-head
and rational stationary barriers. Only their actual value at the constructed
stationary rank remains to be bounded. -/
theorem binary_of_unimodal_stationary {p a c r : ℝ}
    (hp : p ∈ Ioo (0:ℝ) 1) (hlp : lam≤p) (ha : 0≤a) (hal : a<lam)
    (hc : c ∈ Icc (0:ℝ) a) (hr : r ∈ Ico a lam)
    (hup : MonotoneOn (binaryStationaryNumerator phi lam p) (Icc 0 c))
    (hdown : AntitoneOn (binaryStationaryNumerator phi lam p) (Icc c a))
    (hend : 0≤binaryStationaryNumerator phi lam p a)
    (hanti : AntitoneOn (binaryStationaryNumerator phi lam p) (Icc a lam))
    (hroot : binaryStationaryNumerator phi lam p r=0)
    (hzero : p*curvePrimitive phi (1-p)≤lam*curvePrimitive phi p)
    (hbarrier : p*binaryRatio phi lam p r≤curvePrimitive phi p) :
    ∀ q ∈ Icc (0:ℝ) lam,normalizedBinaryTest phi p q≤lam := by
  have hmax := h.binaryRatio_le_stationary_root hp ha hlp hr hanti hroot
  have hrootBound : binaryRatio phi lam p r≤curvePrimitive phi p/p :=
    (le_div_iff₀ hp.1).mpr (by nlinarith only [hbarrier])
  have haBound := (hmax a ⟨le_rfl,hal⟩).trans hrootBound
  have hzeroBound : binaryRatio phi lam p 0≤curvePrimitive phi p/p := by
    have hJ0 : curvePrimitive phi 0=0 := by simp [curvePrimitive]
    unfold binaryRatio
    simp only [zero_add,hJ0,sub_zero]
    exact (div_le_div_iff₀ h.lam_pos hp.1).mpr (by nlinarith only [hzero])
  apply h.binary_above_lam_of_stationary hp hlp hzero
  intro q hq _
  by_cases hqa : q≤a
  · exact (h.binaryRatio_max_endpoints_of_numerator_unimodal hp le_rfl
      (hal.le.trans hlp) hal hc hup hdown hend q ⟨hq.1.le,hqa⟩).trans
      (max_le hzeroBound haBound)
  · exact (hmax q ⟨le_of_not_ge hqa,hq.2⟩).trans hrootBound

end VerifierCurve
end OptimalG
