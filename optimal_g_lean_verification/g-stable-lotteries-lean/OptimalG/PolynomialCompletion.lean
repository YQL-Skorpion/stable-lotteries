import OptimalG.VerifierConditions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv

/-! Exact head and tail polynomials of Appendix C.2. -/
namespace OptimalG
open Set MeasureTheory

noncomputable def headInitial (x J f : ℝ) : ℝ := 2 * J / x - f
noncomputable def headSlope (x J f : ℝ) : ℝ := (f - headInitial x J f) / x
noncomputable def headScore (x J f r : ℝ) : ℝ := headInitial x J f + headSlope x J f * r
noncomputable def headPrimitive (x J f r : ℝ) : ℝ :=
  headInitial x J f * r + headSlope x J f * r ^ 2 / 2

theorem headScore_at_join (x J f : ℝ) (hx : x ≠ 0) : headScore x J f x = f := by
  unfold headScore headSlope
  rw [div_mul_cancel₀ _ hx]
  ring

theorem headPrimitive_at_join (x J f : ℝ) (hx : x ≠ 0) : headPrimitive x J f x = J := by
  simp only [headPrimitive, headSlope, headInitial]
  field_simp
  ring

theorem headPrimitive_hasDerivAt (x J f r : ℝ) :
    HasDerivAt (headPrimitive x J f) (headScore x J f r) r := by
  have hi := hasDerivAt_id r
  have hd := ((hi.const_mul (headInitial x J f)).add
    (((hi.pow 2).const_mul (headSlope x J f)).div_const 2))
  have heq : headInitial x J f * 1 + headSlope x J f * ((2 : ℝ) * r ^ (2 - 1) * 1) / 2 =
      headScore x J f r := by simp [headScore]; ring
  norm_num only [Nat.cast_ofNat, id_eq] at hd
  rw [heq] at hd
  exact hd

theorem headScore_hasDerivAt (x J f r : ℝ) : HasDerivAt (headScore x J f) (headSlope x J f) r := by
  change HasDerivAt (fun r => headInitial x J f + headSlope x J f * r) (headSlope x J f) r
  simpa only [mul_one, id_eq] using ((hasDerivAt_id r).const_mul (headSlope x J f)).const_add (headInitial x J f)

theorem headScore_continuous (x J f : ℝ) : Continuous (headScore x J f) := by
  unfold headScore; fun_prop

theorem headScore_integral (x J f : ℝ) (hx : x ≠ 0) : (∫ r in (0 : ℝ)..x, headScore x J f r) = J := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => headPrimitive_hasDerivAt x J f r) ((headScore_continuous x J f).intervalIntegrable 0 x),
    headPrimitive_at_join x J f hx]
  simp [headPrimitive]

theorem headScore_strictAnti (x J f : ℝ) (hs : headSlope x J f < 0) : StrictAnti (headScore x J f) := by
  intro a b hab
  unfold headScore
  have hh := mul_lt_mul_of_neg_left hab hs
  linarith

theorem headScore_ceiling (x J f lam : ℝ) (hx : 0 < x)
    (h0 : headInitial x J f ≤ lam) (h1 : f ≤ lam - x) :
    ∀ r ∈ Icc (0 : ℝ) x, headScore x J f r ≤ lam - r := by
  intro r hr
  have hj := headScore_at_join x J f (ne_of_gt hx)
  have hm1 := mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr hr.2)
  have hm2 := mul_nonneg (sub_nonneg.mpr h1) hr.1
  have hjr := congrArg (fun u : ℝ => u * r) hj
  have hh : 0 ≤ x * (lam - r - headScore x J f r) := by
    unfold headScore at *
    nlinarith
  have hh' := nonneg_of_mul_nonneg_right hh hx
  linarith

noncomputable def tailOne (z Y H : ℝ) : ℝ := -6 * Y / (1 - z) - 4 * H + 2
noncomputable def tailTwo (z Y H : ℝ) : ℝ := 3 * H - 3 + 6 * Y / (1 - z)
noncomputable def tailCoord (z r : ℝ) : ℝ := (r - z) / (1 - z)
noncomputable def tailScore (z Y H r : ℝ) : ℝ :=
  H + tailOne z Y H * tailCoord z r + tailTwo z Y H * (tailCoord z r) ^ 2
noncomputable def tailPrimitive (z Y H r : ℝ) : ℝ :=
  Y + (1 - z) * (H * tailCoord z r + tailOne z Y H * (tailCoord z r) ^ 2 / 2 +
    tailTwo z Y H * (tailCoord z r) ^ 3 / 3)
noncomputable def tailSlope (z Y H r : ℝ) : ℝ :=
  (tailOne z Y H + 2 * tailTwo z Y H * tailCoord z r) / (1 - z)

@[simp] theorem tailScore_at_join (z Y H : ℝ) : tailScore z Y H z = H := by
  simp [tailScore, tailCoord]
@[simp] theorem tailPrimitive_at_join (z Y H : ℝ) : tailPrimitive z Y H z = Y := by
  simp [tailPrimitive, tailCoord]

theorem tailScore_at_one (z Y H : ℝ) (hz : z ≠ 1) : tailScore z Y H 1 = -1 := by
  have hh : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  simp only [tailScore, tailCoord, div_self hh, mul_one, one_pow, tailOne, tailTwo]
  ring

theorem tailPrimitive_at_one (z Y H : ℝ) (hz : z ≠ 1) : tailPrimitive z Y H 1 = 0 := by
  have hh : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  simp only [tailPrimitive, tailCoord, div_self hh, mul_one, one_pow, tailOne, tailTwo]
  field_simp
  ring

theorem tailCoord_hasDerivAt (z r : ℝ) : HasDerivAt (tailCoord z) (1 / (1 - z)) r :=
  ((hasDerivAt_id r).sub_const z).div_const (1 - z)

theorem tailScore_hasDerivAt (z Y H r : ℝ) : HasDerivAt (tailScore z Y H) (tailSlope z Y H r) r := by
  have hi := tailCoord_hasDerivAt z r
  have hd := (((hi.const_mul (tailOne z Y H)).const_add H).add
    ((hi.pow 2).const_mul (tailTwo z Y H)))
  have heq : tailOne z Y H * (1 / (1 - z)) +
      tailTwo z Y H * ((2 : ℝ) * tailCoord z r ^ (2 - 1) * (1 / (1 - z))) =
      tailSlope z Y H r := by simp only [tailSlope, Nat.reduceSub, pow_one]; ring
  norm_num only [Nat.cast_ofNat] at hd
  rw [heq] at hd
  exact hd

theorem tailPrimitive_hasDerivAt (z Y H r : ℝ) (hz : z ≠ 1) :
    HasDerivAt (tailPrimitive z Y H) (tailScore z Y H r) r := by
  have hh : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hi := tailCoord_hasDerivAt z r
  have hd := ((((hi.const_mul H).add (((hi.pow 2).const_mul (tailOne z Y H)).div_const 2)).add
    (((hi.pow 3).const_mul (tailTwo z Y H)).div_const 3)).const_mul (1 - z)).const_add Y
  have heq : (1 - z) * (H * (1 / (1 - z)) +
      tailOne z Y H * ((2 : ℝ) * tailCoord z r ^ (2 - 1) * (1 / (1 - z))) / 2 +
      tailTwo z Y H * ((3 : ℝ) * tailCoord z r ^ (3 - 1) * (1 / (1 - z))) / 3) = tailScore z Y H r := by
    simp only [tailScore, Nat.reduceSub, pow_one]
    field_simp <;> ring
  norm_num only [Nat.cast_ofNat] at hd
  rw [heq] at hd
  exact hd

theorem tailScore_continuous (z Y H : ℝ) : Continuous (tailScore z Y H) := by
  unfold tailScore tailCoord; fun_prop

theorem tailScore_integral (z Y H : ℝ) (hz : z ≠ 1) :
    (∫ r in z..1, tailScore z Y H r) = -Y := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => tailPrimitive_hasDerivAt z Y H r hz) ((tailScore_continuous z Y H).intervalIntegrable z 1),
    tailPrimitive_at_one z Y H hz, tailPrimitive_at_join]
  ring

theorem tailCoord_mem_Icc (z r : ℝ) (hz : z < 1) (hr : r ∈ Icc z 1) :
    tailCoord z r ∈ Icc (0 : ℝ) 1 := by
  have hh := sub_pos.mpr hz
  constructor
  · exact div_nonneg (sub_nonneg.mpr hr.1) hh.le
  · exact (div_le_one hh).mpr (by linarith [hr.2])

theorem tailScore_strictAntiOn (z Y H : ℝ) (hz : z < 1)
    (h1 : tailOne z Y H < 0) (h2 : tailTwo z Y H ≤ 0) :
    StrictAntiOn (tailScore z Y H) (Icc z 1) := by
  intro a ha b hb hab
  have hwa := (tailCoord_mem_Icc z a hz ha).1
  have hwb := (tailCoord_mem_Icc z b hz hb).1
  have hwab : tailCoord z a < tailCoord z b :=
    (div_lt_div_iff_of_pos_right (sub_pos.mpr hz)).mpr (by linarith)
  have hd : 0 < tailCoord z b - tailCoord z a := sub_pos.mpr hwab
  have hn : tailOne z Y H + tailTwo z Y H * (tailCoord z a + tailCoord z b) < 0 :=
    add_neg_of_neg_of_nonpos h1 (mul_nonpos_of_nonpos_of_nonneg h2 (add_nonneg hwa hwb))
  have hh := mul_neg_of_pos_of_neg hd hn
  unfold tailScore
  nlinarith

/-- The tail slope is no greater than its initial slope when c2≤0. -/
theorem tailSlope_le_join (z Y H : ℝ) (hz : z < 1) (h2 : tailTwo z Y H ≤ 0)
    {r : ℝ} (hr : r ∈ Icc z 1) : tailSlope z Y H r ≤ tailOne z Y H / (1 - z) := by
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hz).le
  have hh := mul_nonpos_of_nonpos_of_nonneg h2 (tailCoord_mem_Icc z r hz hr).1
  linarith


theorem tailSlope_antitone (z Y H : ℝ) (hz : z < 1) (h2 : tailTwo z Y H ≤ 0) :
    Antitone (tailSlope z Y H) := by
  intro a b hab
  have hw : tailCoord z a ≤ tailCoord z b :=
    (div_le_div_iff_of_pos_right (sub_pos.mpr hz)).mpr (by linarith)
  have hh := mul_le_mul_of_nonpos_left hw h2
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hz).le
  linarith

theorem tailScore_concave (z Y H : ℝ) (hz : z < 1) (h2 : tailTwo z Y H ≤ 0) :
    ConcaveOn ℝ (Icc z 1) (tailScore z Y H) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc z 1) (tailScore_continuous z Y H).continuousOn
    (fun r _ => (tailScore_hasDerivAt z Y H r).differentiableAt.differentiableWithinAt)
  intro a ha b hb hab
  rw [(tailScore_hasDerivAt z Y H a).deriv, (tailScore_hasDerivAt z Y H b).deriv]
  exact tailSlope_antitone z Y H hz h2 hab

/-- Uniqueness of the quadratic completion from value, endpoint and area. -/
theorem tailCoefficients_unique (z Y H c1 c2 : ℝ) (hz : z ≠ 1)
    (hend : H + c1 + c2 = -1)
    (harea : Y + (1 - z) * (H + c1 / 2 + c2 / 3) = 0) :
    c1 = tailOne z Y H ∧ c2 = tailTwo z Y H := by
  have hh : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have he1 : c1 * (1 - z) = -6 * Y + (-4 * H + 2) * (1 - z) := by
    nlinarith [congrArg (fun t : ℝ => t * (1 - z)) hend]
  have he2 : c2 * (1 - z) = (3 * H - 3) * (1 - z) + 6 * Y := by
    nlinarith [congrArg (fun t : ℝ => t * (1 - z)) hend]
  constructor
  · unfold tailOne
    apply (mul_left_inj' hh).mp
    field_simp
    nlinarith
  · unfold tailTwo
    apply (mul_left_inj' hh).mp
    field_simp
    nlinarith

noncomputable def tailBackwardSlope (z Y H : ℝ) : ℝ :=
  -(tailOne z Y H + 2 * tailTwo z Y H) / (1 - z)
noncomputable def tailBackwardCurvature (z Y H : ℝ) : ℝ :=
  -tailTwo z Y H / (1 - z) ^ 2

/-- Equation C.10 in backward coordinates. -/
theorem tailScore_backward (z Y H r : ℝ) (hz : z ≠ 1) :
    tailScore z Y H r = -1 + tailBackwardSlope z Y H * (1 - r) -
      tailBackwardCurvature z Y H * (1 - r) ^ 2 := by
  have hh : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  unfold tailScore tailCoord tailBackwardSlope tailBackwardCurvature tailOne tailTwo
  field_simp
  ring

theorem tailPrimitive_backward (z Y H r : ℝ) (hz : z ≠ 1) :
    tailPrimitive z Y H r = (1 - r) - tailBackwardSlope z Y H / 2 * (1 - r) ^ 2 +
      tailBackwardCurvature z Y H / 3 * (1 - r) ^ 3 := by
  have hh : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  unfold tailPrimitive tailCoord tailBackwardSlope tailBackwardCurvature tailOne tailTwo
  field_simp
  ring

end OptimalG
