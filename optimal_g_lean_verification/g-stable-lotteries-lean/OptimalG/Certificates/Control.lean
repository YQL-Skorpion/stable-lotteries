import OptimalG.Certificates.Compact
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Rational control derivatives and certified geometric coefficients

The coordinate A (respectively B) is the score value φ(x) (respectively φ(y));
these derivatives do not assume that the low-rank function is differentiable.
The R/P derivatives are exact identities, followed by the sign implications
used in the variational perturbation argument.
-/

namespace OptimalG.Certificates.Control

noncomputable def det (h k R P : ℝ) : ℝ := h * R - k * P
noncomputable def cx (U k R K : ℝ) : ℝ := U * R + k * K
noncomputable def cy (U h P K : ℝ) : ℝ := U * P + h * K
noncomputable def alphaNumerator (h k A B : ℝ) : ℝ := k * A + h * B

noncomputable def value (U h k R P K A B : ℝ) : ℝ :=
  -(U * (R * A + P * B) + K * alphaNumerator h k A B) / det h k R P

private theorem affine_derivative (a b x : ℝ) :
    HasDerivAt (fun t : ℝ => a * t + b) a x := by
  simpa using ((hasDerivAt_id x).const_mul a).add_const b

private theorem fractional_derivative (a b c d x : ℝ) (hx : c * x + d ≠ 0) :
    HasDerivAt (fun t : ℝ => (a * t + b) / (c * t + d))
      ((a * d - b * c) / (c * x + d) ^ 2) x := by
  have h := (affine_derivative a b x).div (affine_derivative c d x) hx
  have hd : (a * (c * x + d) - (a * x + b) * c) / (c * x + d) ^ 2 =
      (a * d - b * c) / (c * x + d) ^ 2 := by congr 1 <;> ring
  change HasDerivAt (fun t : ℝ => (a * t + b) / (c * t + d))
    ((a * (c * x + d) - (a * x + b) * c) / (c * x + d) ^ 2) x at h
  rw [hd] at h
  exact h

theorem scoreA_derivative (U h k R P K A B : ℝ) :
    HasDerivAt (fun a : ℝ => value U h k R P K a B)
      (-cx U k R K / det h k R P) A := by
  have hf : (fun a : ℝ => value U h k R P K a B) =
      fun a : ℝ => (-cx U k R K / det h k R P) * a + value U h k R P K 0 B := by
    funext a
    unfold value alphaNumerator cx
    ring
  rw [hf]
  exact affine_derivative _ _ _

theorem scoreB_derivative (U h k R P K A B : ℝ) :
    HasDerivAt (fun b : ℝ => value U h k R P K A b)
      (-cy U h P K / det h k R P) B := by
  have hf : (fun b : ℝ => value U h k R P K A b) =
      fun b : ℝ => (-cy U h P K / det h k R P) * b + value U h k R P K A 0 := by
    funext b
    unfold value alphaNumerator cy
    ring
  rw [hf]
  exact affine_derivative _ _ _

theorem K_derivative (U h k R P K A B : ℝ) :
    HasDerivAt (fun kappa : ℝ => value U h k R P kappa A B)
      (-alphaNumerator h k A B / det h k R P) K := by
  have hf : (fun kappa : ℝ => value U h k R P kappa A B) =
      fun kappa : ℝ => (-alphaNumerator h k A B / det h k R P) * kappa +
        value U h k R P 0 A B := by
    funext kappa
    unfold value
    ring
  rw [hf]
  exact affine_derivative _ _ _

theorem R_derivative (U h k R P K A B : ℝ) (hD : det h k R P ≠ 0) :
    HasDerivAt (fun r : ℝ => value U h k r P K A B)
      (alphaNumerator h k A B * cy U h P K / (det h k R P) ^ 2) R := by
  have hx : h * R + -(k * P) ≠ 0 := by simpa [det, sub_eq_add_neg] using hD
  have hd := fractional_derivative (-U * A)
    (-(U * P * B + K * alphaNumerator h k A B)) h (-(k * P)) R hx
  have hf : (fun r : ℝ => value U h k r P K A B) =
      fun r : ℝ => ((-U * A) * r + -(U * P * B + K * alphaNumerator h k A B)) /
        (h * r + -(k * P)) := by
    funext r
    unfold value det
    congr 1 <;> ring
  have he : ((-U * A) * -(k * P) - -(U * P * B + K * alphaNumerator h k A B) * h) /
      (h * R + -(k * P)) ^ 2 =
      alphaNumerator h k A B * cy U h P K / (det h k R P) ^ 2 := by
    unfold alphaNumerator cy det
    congr 1 <;> ring
  rw [hf, ← he]
  exact hd

theorem P_derivative (U h k R P K A B : ℝ) (hD : det h k R P ≠ 0) :
    HasDerivAt (fun p : ℝ => value U h k R p K A B)
      (-alphaNumerator h k A B * cx U k R K / (det h k R P) ^ 2) P := by
  have hx : -k * P + h * R ≠ 0 := by
    have he : -k * P + h * R = det h k R P := by unfold det; ring
    rwa [he]
  have hd := fractional_derivative (-U * B)
    (-(U * R * A + K * alphaNumerator h k A B)) (-k) (h * R) P hx
  have hf : (fun p : ℝ => value U h k R p K A B) =
      fun p : ℝ => ((-U * B) * p + -(U * R * A + K * alphaNumerator h k A B)) /
        (-k * p + h * R) := by
    funext p
    unfold value det
    congr 1 <;> ring
  have he : ((-U * B) * (h * R) - -(U * R * A + K * alphaNumerator h k A B) * -k) /
      (-k * P + h * R) ^ 2 =
      -alphaNumerator h k A B * cx U k R K / (det h k R P) ^ 2 := by
    unfold alphaNumerator cx det
    congr 1 <;> ring
  rw [hf, ← he]
  exact hd

/-- Activity forces positive state slope, using the strict opposite-binary gap. -/
theorem active_alpha_positive (U h k R P K A B : ℝ)
    (hU : 0 < U) (hD : 0 < det h k R P) (hK : 0 ≤ K)
    (hgap : R * A + P * B < det h k R P)
    (hactive : value U h k R P K A B ≤ -U) :
    0 < alphaNumerator h k A B := by
  unfold value at hactive
  have hnum := (div_le_iff₀ hD).mp hactive
  by_contra hn
  have halpha : alphaNumerator h k A B ≤ 0 := le_of_not_gt hn
  have hk := mul_nonpos_of_nonneg_of_nonpos hK halpha
  have hg := mul_lt_mul_of_pos_left hgap hU
  nlinarith

/-- The score ceiling and the strict opposite-binary inequality give the gap
used in `active_alpha_positive`. -/
theorem score_gap (L p x y R P A B : ℝ)
    (hR : 0 ≤ R) (hP : 0 ≤ P) (hA : A ≤ L - x) (hB : B ≤ L - y)
    (hbinary : 0 < L * R - p * P) :
    R * A + P * B < det (2 * L - x) (p + y - L) R P := by
  have hx := mul_nonneg hR (sub_nonneg.mpr hA)
  have hy := mul_nonneg hP (sub_nonneg.mpr hB)
  unfold det
  nlinarith

/-- Numerical geometric coefficients on the admitted high-rank rectangle. -/
theorem coefficients_positive (L p x y z R P K : ℝ)
    (hL : Compact.LambdaRange L)
    (hp : p ∈ Set.Icc (0.25 : ℝ) 0.36)
    (hx : x ≤ 0.38) (hy : 0.285 ≤ y)
    (hz : z ∈ Set.Icc (0.775 : ℝ) 0.875)
    (hR : 0.0826 ≤ R) (hP : 0.113 ≤ P)
    (hK : 0 ≤ K) (hKmax : K ≤ 0.111315) :
    0.0145 < cx (z - L) (p + y - L) R K ∧
    0.024 < cy (z - L) (2 * L - x) P K := by
  have hU : (0.21267 : ℝ) ≤ z - L := by linarith [hz.1, hL.2]
  have hU0 : 0 ≤ z - L := by linarith
  have hk : (-0.027330 : ℝ) ≤ p + y - L := by linarith [hp.1, hy, hL.2]
  have hh : 0 ≤ 2 * L - x := by linarith [hL.1, hx]
  have hUR := mul_le_mul hU hR (by norm_num : (0 : ℝ) ≤ 0.0826) hU0
  have hUP := mul_le_mul hU hP (by norm_num : (0 : ℝ) ≤ 0.113) hU0
  have hk1 := mul_le_mul_of_nonneg_right hk hK
  have hk2 := mul_le_mul_of_nonpos_left hKmax (by norm_num : (-0.027330 : ℝ) ≤ 0)
  have hhK := mul_nonneg hh hK
  unfold cx cy
  constructor <;> nlinarith

end OptimalG.Certificates.Control
