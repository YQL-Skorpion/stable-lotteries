import OptimalG.TailContact

/-! The differential control inequalities survive the quadratic tail (C.11). -/
namespace OptimalG
open Set

/-- A concave quadratic is nonnegative between two nonnegative endpoint values. -/
theorem quadratic_nonneg_between (A B C a b : ℝ) (hC : C ≤ 0)
    (ha : 0 ≤ A + B * a + C * a ^ 2) (hb : 0 ≤ A + B * b + C * b ^ 2) :
    ∀ t ∈ Icc a b, 0 ≤ A + B * t + C * t ^ 2 := by
  intro t ht
  rcases eq_or_lt_of_le (ht.1.trans ht.2) with hab | hab
  · have hta : t = a := by linarith [ht.1, ht.2]
    simpa only [hta] using ha
  · have hleft := mul_nonneg (sub_nonneg.mpr ht.2) ha
    have hright := mul_nonneg (sub_nonneg.mpr ht.1) hb
    have hcurve := mul_nonneg (neg_nonneg.mpr hC)
      (mul_nonneg (sub_pos.mpr hab).le (mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)))
    have hid : (b - a) * (A + B * t + C * t ^ 2) =
        (b - t) * (A + B * a + C * a ^ 2) +
        (t - a) * (A + B * b + C * b ^ 2) + (-C) * ((b - a) * ((t - a) * (b - t))) := by ring
    have hh : 0 ≤ (b - a) * (A + B * t + C * t ^ 2) := by rw [hid]; positivity
    exact nonneg_of_mul_nonneg_right hh (sub_pos.mpr hab)

theorem tailSlope_backward (z Y H r : ℝ) (hz : z ≠ 1) :
    tailSlope z Y H r = -tailBackwardSlope z Y H + 2 * tailBackwardCurvature z Y H * (1 - r) := by
  have hh : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  unfold tailSlope tailCoord tailBackwardSlope tailBackwardCurvature
  field_simp
  ring

noncomputable def tailControlGap (z Y H lam S p theta alpha r : ℝ) : ℝ :=
  -theta * (r - lam) - alpha * (Variational.quadratic lam (r - p) - S - tailPrimitive z Y H r) - tailScore z Y H r
noncomputable def tailControlSlope (v kappa lam p theta alpha r : ℝ) : ℝ :=
  v - theta - alpha * (p + lam) + (alpha * (v - 1) - 2 * kappa) * (1 - r) -
    alpha * kappa * (1 - r) ^ 2

/-- The exact derivative polynomial of C.11. -/
theorem tailControlGap_hasDerivAt (z Y H lam S p theta alpha r : ℝ) (hz : z ≠ 1) :
    HasDerivAt (tailControlGap z Y H lam S p theta alpha)
      (tailControlSlope (tailBackwardSlope z Y H) (tailBackwardCurvature z Y H) lam p theta alpha r) r := by
  have hQ := (Variational.quadratic_hasDerivAt lam (r - p)).comp r ((hasDerivAt_id r).sub_const p)
  have hJ := tailPrimitive_hasDerivAt z Y H r hz
  have hphi := tailScore_hasDerivAt z Y H r
  have hd := ((((hasDerivAt_id r).sub_const lam).const_mul (-theta)).sub
    (((hQ.sub_const S).sub hJ).const_mul alpha)).sub hphi
  have heq : -theta * 1 - alpha * ((lam - (r - p)) * 1 - tailScore z Y H r) - tailSlope z Y H r =
      tailControlSlope (tailBackwardSlope z Y H) (tailBackwardCurvature z Y H) lam p theta alpha r := by
    rw [tailScore_backward z Y H r hz, tailSlope_backward z Y H r hz]
    unfold tailControlSlope
    ring
  change HasDerivAt (tailControlGap z Y H lam S p theta alpha)
    (-theta * 1 - alpha * ((lam - (r - p)) * 1 - tailScore z Y H r) - tailSlope z Y H r) r at hd
  rw [heq] at hd
  exact hd

theorem tailControlSlope_nonneg (z v kappa lam p theta alpha : ℝ)
    (hk : 0 ≤ kappa) (ha : 0 ≤ alpha)
    (hz : 0 ≤ tailControlSlope v kappa lam p theta alpha z)
    (h1 : 0 ≤ tailControlSlope v kappa lam p theta alpha 1) :
    ∀ r ∈ Icc z 1, 0 ≤ tailControlSlope v kappa lam p theta alpha r := by
  intro r hr
  have hh := quadratic_nonneg_between (v - theta - alpha * (p + lam))
    (alpha * (v - 1) - 2 * kappa) (-alpha * kappa) 0 (1 - z)
    (by nlinarith [mul_nonneg ha hk])
    (by simpa [tailControlSlope] using h1)
    (by simpa [tailControlSlope, sub_eq_add_neg, neg_mul] using hz)
    (1 - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
  simpa only [tailControlSlope, neg_mul, sub_eq_add_neg] using hh

/-- Endpoint checks of the derivative polynomial propagate the actual control bound through the tail. -/
theorem tailControl_preserved (z Y H lam S p theta alpha : ℝ) (hz : z < 1)
    (hk : 0 ≤ tailBackwardCurvature z Y H) (ha : 0 ≤ alpha)
    (hstart : 0 ≤ tailControlGap z Y H lam S p theta alpha z)
    (hslopeStart : 0 ≤ tailControlSlope (tailBackwardSlope z Y H) (tailBackwardCurvature z Y H) lam p theta alpha z)
    (hslopeEnd : 0 ≤ tailControlSlope (tailBackwardSlope z Y H) (tailBackwardCurvature z Y H) lam p theta alpha 1) :
    ∀ r ∈ Icc z 1, tailScore z Y H r ≤
      -theta * (r - lam) - alpha * (Variational.quadratic lam (r - p) - S - tailPrimitive z Y H r) := by
  have hdiff (r : ℝ) := tailControlGap_hasDerivAt z Y H lam S p theta alpha r (ne_of_lt hz)
  have hcont : Continuous (tailControlGap z Y H lam S p theta alpha) :=
    continuous_iff_continuousAt.mpr (fun r => (hdiff r).continuousAt)
  have hmono : MonotoneOn (tailControlGap z Y H lam S p theta alpha) (Icc z 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc z 1) hcont.continuousOn
      (fun r _ => (hdiff r).differentiableAt.differentiableWithinAt)
    intro r hr
    rw [(hdiff r).deriv]
    exact tailControlSlope_nonneg z _ _ lam p theta alpha hk ha hslopeStart hslopeEnd r
      (interior_subset hr)
  intro r hr
  have hh := hstart.trans (hmono ⟨le_rfl, hz.le⟩ hr hr.1)
  exact sub_nonneg.mp hh

end OptimalG
