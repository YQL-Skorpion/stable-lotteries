import OptimalG.Certificates.Control

/-! Active-control slope bounds before the running envelope, when scores may be negative. -/
namespace OptimalG.Certificates.Control
open Set

/-- The nonnegative-k numerator estimate uses only upper score bounds. -/
theorem alphaNumerator_upper_of_k_nonneg {L p x y A B : ℝ}
    (hL : Compact.LambdaRange L) (hx : x ∈ Icc (0.285 : ℝ) 0.38)
    (hy : y ∈ Icc (0.285 : ℝ) 0.38) (hpy : p ≤ y)
    (hk : 0 ≤ p + y - L) (hA : A ≤ L - x) (hB : B ≤ L - y) :
    alphaNumerator (2 * L - x) (p + y - L) A B ≤ (0.562330 : ℝ) ^ 2 - 0.285 ^ 2 := by
  have hh : 0 ≤ 2 * L - x := by linarith [hL.1, hx.2]
  have ha := mul_le_mul_of_nonneg_left hA hk
  have hb := mul_le_mul_of_nonneg_left hB hh
  have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hpy)
    (show 0 ≤ L - x by linarith [hL.1, hx.2])
  have hxy := mul_le_mul hx.1 hy.1 (by norm_num : (0 : ℝ) ≤ 0.285) (by linarith [hx.1])
  have hsq := mul_nonneg (sub_nonneg.mpr hL.2) (show 0 ≤ 0.562330 + L by linarith [hL.1])
  unfold alphaNumerator
  nlinarith

/-- Multiplying the active inequality by negative k gives the useful bound
M*c_x ≤ U*Delta*p, without any lower bound on either score. -/
theorem active_negative_k_product {L p x y U R P K A B : ℝ}
    (hk : p + y - L ≤ 0) (hU : 0 ≤ U)
    (hD : 0 < det (2 * L - x) (p + y - L) R P)
    (hB : B ≤ L - y)
    (hactive : value U (2 * L - x) (p + y - L) R P K A B ≤ -U) :
    alphaNumerator (2 * L - x) (p + y - L) A B * cx U (p + y - L) R K ≤
      U * det (2 * L - x) (p + y - L) R P * p := by
  have he := (div_le_iff₀ hD).mp hactive
  have hkm := mul_le_mul_of_nonpos_left he hk
  have hbm := mul_le_mul_of_nonneg_left hB (mul_nonneg hU hD.le)
  unfold det cx alphaNumerator at *
  nlinarith

/-- Both calibrated phase bounds remain valid for arbitrary real low-rank
scores, provided the control is active and the scores obey their ceilings. -/
theorem active_phase_slopes {L p x y U R P K A B : ℝ}
    (hL : Compact.LambdaRange L) (hp : p ∈ Icc (0.25 : ℝ) 0.36)
    (hx : x ∈ Icc (0.285 : ℝ) 0.38) (hy : y ∈ Icc (0.285 : ℝ) 0.38) (hpy : p ≤ y)
    (hU : U ∈ Icc (0.21267 : ℝ) 0.313) (hR : R ∈ Icc (0.0826 : ℝ) 0.136)
    (hK : K ∈ Icc (0 : ℝ) 0.159)
    (hD : 0.0519 < det (2 * L - x) (p + y - L) R P)
    (hcx : 0 < cx U (p + y - L) R K)
    (hA : A ≤ L - x) (hB : B ≤ L - y)
    (hactive : value U (2 * L - x) (p + y - L) R P K A B ≤ -U) :
    alphaNumerator (2 * L - x) (p + y - L) A B / det (2 * L - x) (p + y - L) R P < 4.53 ∧
    alphaNumerator (2 * L - x) (p + y - L) A B * cx U (p + y - L) R K /
      (det (2 * L - x) (p + y - L) R P) ^ 2 < 6.19 := by
  let D := det (2 * L - x) (p + y - L) R P
  let M := alphaNumerator (2 * L - x) (p + y - L) A B
  let X := cx U (p + y - L) R K
  have hD0 : 0 < D := by dsimp [D]; linarith
  have hU0 : 0 < U := by linarith [hU.1]
  change M / D < 4.53 ∧ M * X / D ^ 2 < 6.19
  rw [div_lt_iff₀ hD0, div_lt_iff₀ (sq_pos_of_pos hD0)]
  have hMb : M < 0 → M < 4.53 * D ∧ M * X < 6.19 * D ^ 2 := by
    intro hm
    have hprod := mul_neg_of_neg_of_pos hm hcx
    constructor <;> nlinarith [sq_nonneg D]
  by_cases hM : M < 0
  · exact hMb hM
  have hM0 := le_of_not_gt hM
  by_cases hk : 0 ≤ p + y - L
  · have hnum : M ≤ (0.562330 : ℝ) ^ 2 - 0.285 ^ 2 :=
      alphaNumerator_upper_of_k_nonneg hL hx hy hpy hk hA hB
    have hup := mul_le_mul hU.2 hR.2 (show 0 ≤ R by linarith [hR.1]) (by norm_num : (0 : ℝ) ≤ 0.313)
    have hkhi : p + y - L ≤ 0.178 := by linarith [hp.2, hy.2, hL.1]
    have hkprod := mul_le_mul hkhi hK.2 hK.1 (by norm_num : (0 : ℝ) ≤ 0.178)
    have hX : X ≤ 0.313 * 0.136 + 0.178 * 0.159 := by dsimp [X, cx]; linarith
    have hmprod := mul_le_mul hnum hX hcx.le (by norm_num : (0 : ℝ) ≤ 0.562330 ^ 2 - 0.285 ^ 2)
    change 0.0519 < D at hD
    constructor <;> nlinarith
  · have hprod : M * X ≤ U * D * p := active_negative_k_product (le_of_not_ge hk) hU0.le hD0 hB hactive
    have hpl : p ≤ 0.27733 := by linarith [hL.2, hy.1]
    have hklo : -0.02733 ≤ p + y - L := by linarith [hp.1, hy.1, hL.2]
    have hkr := mul_le_mul_of_nonneg_right hklo hK.1
    have hkr' := mul_le_mul_of_nonpos_left hK.2 (by norm_num : (-0.02733 : ℝ) ≤ 0)
    have hrr := mul_le_mul_of_nonneg_left hR.1 hU0.le
    have hXlo : 0.062 * U ≤ X := by dsimp [X, cx]; nlinarith [hU.1]
    have hmx := mul_le_mul_of_nonneg_left hXlo hM0
    have hcancel : 0.062 * M ≤ D * p := by
      apply (mul_le_mul_iff_of_pos_left hU0).mp
      nlinarith
    have hdp := mul_le_mul_of_nonneg_left hpl hD0.le
    have hup := mul_le_mul hU.2 hpl (show 0 ≤ p by linarith [hp.1]) (by norm_num : (0 : ℝ) ≤ 0.313)
    have hscaled := mul_le_mul_of_nonneg_right hup hD0.le
    change 0.0519 < D at hD
    have hgap := mul_pos hD0 (show 0 < 6.19 * D - 0.313 * 0.27733 by linarith)
    constructor <;> nlinarith

end OptimalG.Certificates.Control
