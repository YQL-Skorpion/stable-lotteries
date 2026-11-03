import OptimalG.Certificates.GeneratedSlater
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Exact weighted Slater witness on [0.28, 0.385]

This module turns the generated interval certificate into a theorem about the
actual rational functions in Appendix B.2 and Lemma D.1(ii). It also verifies
the primitive, its derivative, the endpoint area, and the score constraints.
The slack parameter is S = 0.026 and the uniform ceiling slack is 0.001.
-/

namespace OptimalG.Certificates

noncomputable def quadratic (L r : ℝ) : ℝ := L * r - r ^ 2 / 2

/-- The expanded form of the cap C_{λ,S}. -/
noncomputable def cap (L S r : ℝ) : ℝ :=
  L ^ 2 - L / 2 + L * r / 2 - L * S / (1 - r)

theorem cap_eq_quotient (L S r : ℝ) (hr : r ≠ 1) :
    cap L S r = L * (quadratic L (1 - r) - S) / (1 - r) := by
  have hd : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  unfold cap quadratic
  field_simp
  ring

theorem cap_difference (L S a u : ℝ) (ha : 1 - a ≠ 0) (hau : 1 - a - u ≠ 0) :
    cap L S (a + u) - cap L S a =
      L * u / 2 - L * S * u / ((1 - a - u) * (1 - a)) := by
  unfold cap
  have hden : 1 - (a + u) = 1 - a - u := by ring
  rw [hden]
  field_simp [ha, hau]
  ring

namespace Slater

noncomputable def amplitude (L : ℝ) : ℝ :=
  3 * ((0.026 - quadratic L 0.28 + cap L 0.026 0.28) / 0.105 - 0.001)

noncomputable def score (L t : ℝ) : ℝ :=
  L - t - (0.001 + amplitude L * (1 - (t - 0.28) / 0.105) ^ 2)

noncomputable def primitive (L t : ℝ) : ℝ :=
  cap L 0.026 0.28 + (L - 0.28 - 0.001 - amplitude L) * (t - 0.28) +
    (amplitude L / 0.105 - 1 / 2) * (t - 0.28) ^ 2 -
    amplitude L / (3 * 0.105 ^ 2) * (t - 0.28) ^ 3

/-- Continuous extension of (C(t) - F(t))/(t - 0.28) at the left endpoint. -/
noncomputable def gapQuotient (L u : ℝ) : ℝ :=
  0.28 - L / 2 + u / 2 + 0.001 +
    amplitude L * (1 - u / 0.105 + u ^ 2 / (3 * 0.105 ^ 2)) -
    L * 0.026 / ((0.72 - u) * 0.72)

/-- Connect the checked expression to the actual formula, without an oracle. -/
theorem gapExpr_eval (L u : ℝ) :
    GeneratedSlater.gapExpr.eval ![L, u] = gapQuotient L u := by
  norm_num [GeneratedSlater.gapExpr, RatExpr.eval, gapQuotient, amplitude, cap,
    quadratic, div_eq_mul_inv]
  ring

/-- The full strict 0.0033 weighted primitive margin asserted in Lemma D.1(ii). -/
theorem gapQuotient_gt (L u : ℝ)
    (hL : L ∈ Set.Icc (0.562325 : ℝ) 0.562330)
    (hu : u ∈ Set.Icc (0 : ℝ) 0.105) : 0.0033 < gapQuotient L u := by
  have hx : ∀ i, (GeneratedSlater.domain i).Contains (![L, u] i) := by
    intro i
    fin_cases i
    · norm_num [GeneratedSlater.domain, RatInterval.Contains] at *
      exact hL
    · norm_num [GeneratedSlater.domain, RatInterval.Contains] at *
      exact hu
  have h := BoxCertificate.checkLower_sound GeneratedSlater.gapExpr (33 / 10000)
    GeneratedSlater.gapCertificate GeneratedSlater.domain GeneratedSlater.gap_checked ![L, u] hx
  rw [gapExpr_eval] at h
  norm_num at h ⊢
  exact h

/-- A simple exact bound used for the score constraints. -/
theorem amplitude_bounds (L : ℝ) (hL : L ∈ Set.Icc (0.562325 : ℝ) 0.562330) :
    0 < amplitude L ∧ amplitude L < 0.033 := by
  rcases hL with ⟨hl, hu⟩
  have hsq := sq_nonneg (L - 0.562325)
  have hcross := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu)
  norm_num [amplitude, quadratic, cap] at *
  constructor <;> nlinarith

theorem score_bounds (L t : ℝ)
    (hL : L ∈ Set.Icc (0.562325 : ℝ) 0.562330)
    (ht : t ∈ Set.Icc (0.28 : ℝ) 0.385) :
    0.14 < score L t ∧ score L t ≤ L - t - 0.001 := by
  have hA := amplitude_bounds L hL
  have hz : 0 ≤ 1 - (t - 0.28) / 0.105 ∧ 1 - (t - 0.28) / 0.105 ≤ 1 := by
    constructor <;> norm_num at * <;> linarith [ht.1, ht.2]
  have hsq0 := sq_nonneg (1 - (t - 0.28) / 0.105)
  have hsq1 : (1 - (t - 0.28) / 0.105) ^ 2 ≤ 1 := by nlinarith [hz.1, hz.2]
  have hterm0 := mul_nonneg (le_of_lt hA.1) hsq0
  have hterm1 := mul_le_mul_of_nonneg_left hsq1 (le_of_lt hA.1)
  unfold score
  constructor <;> nlinarith [hL.1, ht.2]

theorem primitive_left (L : ℝ) : primitive L 0.28 = cap L 0.026 0.28 := by
  norm_num [primitive]

theorem primitive_right (L : ℝ) : primitive L 0.385 = quadratic L 0.385 - 0.026 := by
  norm_num [primitive, amplitude, quadratic, cap]
  ring

theorem primitive_hasDerivAt (L t : ℝ) : HasDerivAt (primitive L) (score L t) t := by
  have hu : HasDerivAt (fun r : ℝ => r - 0.28) 1 t := (hasDerivAt_id t).sub_const 0.28
  have h := (((hu.const_mul (L - 0.28 - 0.001 - amplitude L)).add
      ((hu.pow 2).const_mul (amplitude L / 0.105 - 1 / 2))).sub
      ((hu.pow 3).const_mul (amplitude L / (3 * 0.105 ^ 2)))).const_add
      (cap L 0.026 0.28)
  change HasDerivAt (fun r : ℝ => cap L 0.026 0.28 +
      ((L - 0.28 - 0.001 - amplitude L) * (r - 0.28) +
      (amplitude L / 0.105 - 1 / 2) * (r - 0.28) ^ 2 -
      amplitude L / (3 * 0.105 ^ 2) * (r - 0.28) ^ 3))
    ((L - 0.28 - 0.001 - amplitude L) * 1 +
      (amplitude L / 0.105 - 1 / 2) * (2 * (t - 0.28) ^ (2 - 1) * 1) -
      amplitude L / (3 * 0.105 ^ 2) * (3 * (t - 0.28) ^ (3 - 1) * 1)) t at h
  have hf : (fun r : ℝ => cap L 0.026 0.28 +
      ((L - 0.28 - 0.001 - amplitude L) * (r - 0.28) +
      (amplitude L / 0.105 - 1 / 2) * (r - 0.28) ^ 2 -
      amplitude L / (3 * 0.105 ^ 2) * (r - 0.28) ^ 3)) = primitive L := by
    funext r
    unfold primitive
    ring
  have hd : (L - 0.28 - 0.001 - amplitude L) * 1 +
      (amplitude L / 0.105 - 1 / 2) * (2 * (t - 0.28) ^ (2 - 1) * 1) -
      amplitude L / (3 * 0.105 ^ 2) * (3 * (t - 0.28) ^ (3 - 1) * 1) = score L t := by
    unfold score
    norm_num
    ring
  rw [hf, hd] at h
  exact h

/-- Exact algebra links the quotient certificate to the primitive cap. -/
theorem cap_sub_primitive (L u : ℝ) (hu : u ≠ 0.72) :
    cap L 0.026 (0.28 + u) - primitive L (0.28 + u) = u * gapQuotient L u := by
  have hd : 1 - (0.28 : ℝ) - u ≠ 0 := by
    intro h
    apply hu
    linarith
  have hc := cap_difference L 0.026 0.28 u (by norm_num) hd
  norm_num at hc
  simp only [primitive, gapQuotient]
  have hshift : (0.28 : ℝ) + u - 0.28 = u := by ring
  rw [hshift]
  norm_num
  linear_combination hc

/-- The weighted cap constraint, including equality at the initial rank. -/
theorem primitive_cap_margin (L t : ℝ)
    (hL : L ∈ Set.Icc (0.562325 : ℝ) 0.562330)
    (ht : t ∈ Set.Icc (0.28 : ℝ) 0.385) :
    0.0033 * (t - 0.28) ≤ cap L 0.026 t - primitive L t := by
  have hu : t - 0.28 ∈ Set.Icc (0 : ℝ) 0.105 := by
    constructor <;> linarith [ht.1, ht.2]
  have hg := gapQuotient_gt L (t - 0.28) hL hu
  have hn : t - 0.28 ≠ 0.72 := by linarith [hu.2]
  have hid := cap_sub_primitive L (t - 0.28) hn
  have heq : (0.28 : ℝ) + (t - 0.28) = t := by ring
  rw [heq] at hid
  rw [hid]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (le_of_lt hg) hu.1

/-- Strict weighted Slater cap condition away from the forced left contact. -/
theorem weighted_cap_strict (L t : ℝ)
    (hL : L ∈ Set.Icc (0.562325 : ℝ) 0.562330)
    (ht : t ∈ Set.Ioc (0.28 : ℝ) 0.385) :
    (primitive L t - cap L 0.026 t) / (t - 0.28) < -0.0033 := by
  have hu : t - 0.28 ∈ Set.Icc (0 : ℝ) 0.105 := by
    constructor <;> linarith [ht.1, ht.2]
  have hg := gapQuotient_gt L (t - 0.28) hL hu
  have hn : t - 0.28 ≠ 0.72 := by linarith [hu.2]
  have hid := cap_sub_primitive L (t - 0.28) hn
  have heq : (0.28 : ℝ) + (t - 0.28) = t := by ring
  rw [heq] at hid
  have htpos : 0 < t - 0.28 := sub_pos.mpr ht.1
  apply (div_lt_iff₀ htpos).mpr
  have hm := mul_lt_mul_of_pos_left hg htpos
  nlinarith

/-- The trial primitive is exactly the integral primitive at every rank. -/
theorem primitive_integral (L t : ℝ) :
    cap L 0.026 0.28 + (∫ r in (0.28 : ℝ)..t, score L r) = primitive L t := by
  have hc : Continuous (score L) := by unfold score; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => primitive_hasDerivAt L r) (hc.intervalIntegrable 0.28 t), primitive_left]
  ring

/-- The constructed polynomial score has the required exact endpoint area. -/
theorem score_integral (L : ℝ) :
    (∫ t in (0.28 : ℝ)..0.385, score L t) =
      quadratic L 0.385 - 0.026 - cap L 0.026 0.28 := by
  have hc : Continuous (score L) := by unfold score; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => primitive_hasDerivAt L t) (hc.intervalIntegrable 0.28 0.385),
    primitive_right, primitive_left]

/-- A genuine strict feasible witness for the low-rank constraints. The score
and its primitive are explicit polynomials; numerical margins are proved above. -/
theorem strict_witness (L : ℝ) (hL : L ∈ Set.Icc (0.562325 : ℝ) 0.562330) :
    (28711863873 / 1306700000000 : ℝ) < 0.026 ∧
    (0.026 : ℝ) < 0.0266503148804352 - (0.562330 - L) / 2 ∧
    Continuous (score L) ∧
    (∀ t ∈ Set.Icc (0.28 : ℝ) 0.385,
      0.14 < score L t ∧ score L t ≤ L - t - 0.001) ∧
    (∀ t : ℝ, cap L 0.026 0.28 + (∫ r in (0.28 : ℝ)..t, score L r) = primitive L t) ∧
    primitive L 0.385 = quadratic L 0.385 - 0.026 ∧
    (∀ t ∈ Set.Ioc (0.28 : ℝ) 0.385,
      (primitive L t - cap L 0.026 t) / (t - 0.28) < -0.0033) := by
  refine ⟨by norm_num, ?_, ?_, ?_, primitive_integral L, primitive_right L, ?_⟩
  · linarith [hL.1]
  · unfold score
    fun_prop
  · exact fun t ht => score_bounds L t hL ht
  · exact fun t ht => weighted_cap_strict L t hL ht

end Slater
end OptimalG.Certificates
