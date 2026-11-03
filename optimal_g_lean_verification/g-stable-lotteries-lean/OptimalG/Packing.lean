import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Packing a prescribed mass against the right endpoint

This proves the one-dimensional rearrangement inequality used in (5.8).
It applies to arbitrary integrable fractional occupation functions, not just
unions of candidate intervals. Finite rank intervals will supply the occupation.
-/

namespace OptimalG

open MeasureTheory Set
open scoped Interval

theorem intervalIntegrable_on_subinterval {f : ℝ → ℝ} {a b c d : ℝ}
    (hf : IntervalIntegrable f volume a b) (hab : a ≤ b)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    IntervalIntegrable f volume c d := by
  apply hf.mono_set
  rw [uIcc_of_le hcd, uIcc_of_le hab]
  exact Icc_subset_Icc hac hdb

/-- Among occupations in `[0,1]` of mass `b-c`, an increasing score has largest
integral when that occupation fills `[c,b]`. -/
theorem pack_right (f w : ℝ → ℝ) (a c b : ℝ)
    (hac : a ≤ c) (hcb : c ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hmono : MonotoneOn f (Icc a b))
    (hw : IntervalIntegrable w volume a b)
    (hwb : ∀ x ∈ Icc a b, 0 ≤ w x ∧ w x ≤ 1)
    (hmass : (∫ x in a..b, w x) = b - c) :
    (∫ x in a..b, w x * f x) ≤ ∫ x in c..b, f x := by
  have hab : a ≤ b := le_trans hac hcb
  have hcc : c ∈ Icc a b := ⟨hac, hcb⟩
  have hfu : ContinuousOn f (uIcc a b) := by simpa [uIcc_of_le hab] using hf
  have hfw : IntervalIntegrable (fun x => w x * f x) volume a b :=
    hw.mul_continuousOn hfu
  have hfbar : IntervalIntegrable (fun x => f x - f c) volume a b :=
    (hf.sub continuousOn_const).intervalIntegrable_of_Icc hab
  have hwbar : IntervalIntegrable (fun x => w x * (f x - f c)) volume a b :=
    hw.mul_continuousOn (hfu.sub continuousOn_const)
  have hwbarLeft := intervalIntegrable_on_subinterval hwbar hab le_rfl hac hcb
  have hwbarRight := intervalIntegrable_on_subinterval hwbar hab hac hcb le_rfl
  have hfbarRight := intervalIntegrable_on_subinterval hfbar hab hac hcb le_rfl
  have hleft : (∫ x in a..c, w x * (f x - f c)) ≤ 0 := by
    have hh := intervalIntegral.integral_mono_on hac hwbarLeft
      (intervalIntegrable_const (c := (0 : ℝ))) (fun x hx => ?_)
    · simpa using hh
    · have hxab : x ∈ Icc a b := ⟨hx.1, le_trans hx.2 hcb⟩
      exact mul_nonpos_of_nonneg_of_nonpos (hwb x hxab).1
        (sub_nonpos.mpr (hmono hxab hcc hx.2))
  have hright : (∫ x in c..b, w x * (f x - f c)) ≤
      ∫ x in c..b, (f x - f c) := by
    apply intervalIntegral.integral_mono_on hcb hwbarRight hfbarRight
    intro x hx
    have hxab : x ∈ Icc a b := ⟨le_trans hac hx.1, hx.2⟩
    have hnonneg : 0 ≤ f x - f c := sub_nonneg.mpr (hmono hcc hxab hx.1)
    simpa using mul_le_mul_of_nonneg_right (hwb x hxab).2 hnonneg
  have hwhole : (∫ x in a..b, w x * (f x - f c)) ≤
      ∫ x in c..b, (f x - f c) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hwbarLeft hwbarRight]
    linarith
  have hfRight : IntervalIntegrable f volume c b :=
    intervalIntegrable_on_subinterval (hf.intervalIntegrable_of_Icc hab) hab hac hcb le_rfl
  have hrewrite : (∫ x in a..b, w x * (f x - f c)) =
      (∫ x in a..b, w x * f x) - (b - c) * f c := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hfw (hw.mul_const (f c)),
      intervalIntegral.integral_mul_const, hmass]
  rw [hrewrite, intervalIntegral.integral_sub hfRight intervalIntegrable_const,
    intervalIntegral.integral_const] at hwhole
  simpa only [smul_eq_mul] using (sub_le_sub_iff_right ((b - c) * f c)).mp hwhole

/-- The equivalent lower bound for a decreasing curve, the sign used for φ in (5.8). -/
theorem pack_right_antitone (phi w : ℝ → ℝ) (a c b : ℝ)
    (hac : a ≤ c) (hcb : c ≤ b)
    (hphi : ContinuousOn phi (Icc a b)) (hanti : AntitoneOn phi (Icc a b))
    (hw : IntervalIntegrable w volume a b)
    (hwb : ∀ x ∈ Icc a b, 0 ≤ w x ∧ w x ≤ 1)
    (hmass : (∫ x in a..b, w x) = b - c) :
    (∫ x in c..b, phi x) ≤ ∫ x in a..b, w x * phi x := by
  have hmono : MonotoneOn (fun x => -phi x) (Icc a b) := by
    intro x hx y hy hxy
    exact neg_le_neg (hanti hx hy hxy)
  have h := pack_right (fun x => -phi x) w a c b hac hcb hphi.neg hmono hw hwb hmass
  simp only [mul_neg, intervalIntegral.integral_neg, neg_le_neg_iff] at h
  exact h

end OptimalG
