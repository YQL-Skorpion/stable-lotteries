import OptimalG.BinaryDerivativeReduction
import OptimalG.DefectBounds

/-! The high-split end of C.3 follows from actual score concavity and the
low-split inequality at λ. No additional numerical split certificate is used. -/
namespace OptimalG
open Set MeasureTheory

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem highScore_chord (hc : ConcaveOn ℝ (Icc lam 1) phi) :
    ∀ r ∈ Icc lam 1, -(r-lam)/(1-lam) ≤ phi r := by
  intro r hr
  have hd : 0 < 1-lam := sub_pos.mpr h.lam_lt_one
  have hsum : (1-r)/(1-lam)+(r-lam)/(1-lam)=1 := by field_simp; ring
  have hid : (1-r)/(1-lam)*lam+(r-lam)/(1-lam)*1=r := by field_simp; ring
  have hh := hc.2 (left_mem_Icc.mpr h.lam_lt_one.le) (right_mem_Icc.mpr h.lam_lt_one.le)
    (div_nonneg (sub_nonneg.mpr hr.2) hd.le)
    (div_nonneg (sub_nonneg.mpr hr.1) hd.le) hsum
  simpa only [smul_eq_mul,hid,h.at_lam,h.at_one,mul_zero,zero_add,mul_neg_one,neg_div] using hh

theorem primitive_high_chord_bound (hc : ConcaveOn ℝ (Icc lam 1) phi)
    {p : ℝ} (hp : p ∈ Icc lam 1) :
    curvePrimitive phi p ≤ (1-p)-(1-p)^2/(2*(1-lam)) := by
  have hd : 1-lam ≠ 0 := (sub_pos.mpr h.lam_lt_one).ne'
  let F := fun u : ℝ => -(u-lam)^2/(2*(1-lam))
  have hF (u : ℝ) : HasDerivAt F (-(u-lam)/(1-lam)) u := by
    convert! ((((hasDerivAt_id u).sub_const lam).pow 2).neg.div_const (2*(1-lam))) using 1 <;>
      first | rfl | (simp only [id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one]; field_simp <;> ring)
  have hi : IntervalIntegrable (fun u : ℝ => -(u-lam)/(1-lam)) volume p 1 :=
    (by fun_prop : Continuous (fun u : ℝ => -(u-lam)/(1-lam))).intervalIntegrable p 1
  have hint : (∫ u in p..1, -(u-lam)/(1-lam))= -(1-p)+(1-p)^2/(2*(1-lam)) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hF u) hi]
    dsimp [F]
    field_simp
    ring
  have hh := intervalIntegral.integral_mono_on hp.2 hi
    (h.integral_subinterval (h.lam_pos.le.trans hp.1) hp.2 le_rfl)
    (fun u hu => h.highScore_chord hc u ⟨hp.1.trans hu.1,hu.2⟩)
  rw [hint,←h.primitive_difference (h.lam_pos.le.trans hp.1) hp.2 le_rfl] at hh
  have hz : curvePrimitive phi 1=0 := h.integral_zero
  rw [hz] at hh
  linarith

theorem primitive_le_mass_tail (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (hl : 1/2 ≤ lam) {p : ℝ} (hp : p ∈ Icc lam 1) :
    curvePrimitive phi p ≤ p*(1-p) := by
  have hh := h.primitive_high_chord_bound hc hp
  have hd : 0 < 2*(1-lam) := by linarith [h.lam_lt_one]
  have hsq : (1-p)^2 ≤ (1-p)^2/(2*(1-lam)) := by
    apply (le_div_iff₀ hd).mpr
    have hm := mul_le_mul_of_nonneg_left (show 2*(1-lam) ≤ 1 by linarith) (sq_nonneg (1-p))
    simpa only [mul_one] using hm
  nlinarith only [hh,hsq]

theorem normalizedBinaryTest_high_antitone (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (hl : 1/2 ≤ lam) {p : ℝ} (hp : p ∈ Ioo lam 1) :
    AntitoneOn (normalizedBinaryTest phi p) (Icc lam p) := by
  have hp0 : p ∈ Ioo (0:ℝ) 1 := ⟨h.lam_pos.trans hp.1,hp.2⟩
  have hJ := h.primitive_pos hp0
  apply antitoneOn_of_deriv_nonpos (convex_Icc lam p)
    (h.normalizedBinaryTest_continuousOn hp0 h.lam_pos.le le_rfl)
    (fun q hq => by
      rw [interior_Icc] at hq
      exact (h.normalizedBinaryTest_hasDerivAt hp0 (h.lam_pos.trans hq.1) hq.2).differentiableAt.differentiableWithinAt)
  intro q hq
  rw [interior_Icc] at hq
  rw [(h.normalizedBinaryTest_hasDerivAt hp0 (h.lam_pos.trans hq.1) hq.2).deriv]
  have hfall := h.high_fall q (q+1-p) hq.1.le (by linarith [hp.2]) (by linarith [hq.2])
  have hm := mul_le_mul_of_nonneg_left hfall hp0.1.le
  have hupper := h.primitive_le_mass_tail hc hl ⟨hp.1.le,hp.2.le⟩
  have hnum : p*(phi (q+1-p)-phi q) ≤ -curvePrimitive phi p := by nlinarith only [hm,hupper]
  have hh := (div_le_div_of_nonneg_right hnum hJ.le)
  rw [←div_mul_eq_mul_div] at hh
  have he : (-curvePrimitive phi p)/curvePrimitive phi p= -1 := by simp [hJ.ne']
  rw [he] at hh
  linarith

/-- Once all low splits are checked, concavity covers every split up to p. -/
theorem binary_all_splits_of_low (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (hl : 1/2 ≤ lam) {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1)
    (hlow : ∀ q, 0 ≤ q → q ≤ p → q ≤ lam → normalizedBinaryTest phi p q ≤ lam) :
    ∀ q ∈ Icc (0:ℝ) p, normalizedBinaryTest phi p q ≤ lam := by
  intro q hq
  by_cases hql : q ≤ lam
  · exact hlow q hq.1 hq.2 hql
  · have hlp : lam < p := (lt_of_not_ge hql).trans_le hq.2
    exact ((h.normalizedBinaryTest_high_antitone hc hl ⟨hlp,hp.2⟩)
      ⟨le_rfl,hlp.le⟩ ⟨(lt_of_not_ge hql).le,hq.2⟩ (lt_of_not_ge hql).le).trans
      (hlow lam h.lam_pos.le hlp.le le_rfl)

end VerifierCurve
end OptimalG
