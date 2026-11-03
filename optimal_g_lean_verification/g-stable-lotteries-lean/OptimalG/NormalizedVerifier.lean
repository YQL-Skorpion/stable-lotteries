import OptimalG.VerifierConditions

/-! Exact normalized forms C.1--C.3 of the two high-rank verifier inequalities. -/
namespace OptimalG
open Set

noncomputable def lowRankRatio (phi : ℝ → ℝ) (lam x : ℝ) : ℝ := (lam - x) / phi x
noncomputable def correctionRatio (phi : ℝ → ℝ) (c x : ℝ) : ℝ := c / phi x

theorem normalized_high_first_low {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    {x q B c : ℝ} (hx : x ∈ Ico (0 : ℝ) lam) (hq : q ∈ Icc (0 : ℝ) lam) :
    (phi x * (q + B + rankPotential phi lam x q - lam) ≤ max (-phi q) 0 * c) ↔ q + B ≤ lam := by
  rw [rankPotential_low phi lam x q hq.2,
    max_eq_right (neg_nonpos.mpr (h.nonnegative hq)), zero_mul, add_zero]
  constructor
  · intro hh
    have hh' := nonpos_of_mul_nonpos_right hh (h.positive hx)
    linarith
  · intro hh
    exact mul_nonpos_of_nonneg_of_nonpos (h.positive hx).le (by linarith)

theorem normalized_high_first_high {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    {x q B c : ℝ} (hx : x ∈ Ico (0 : ℝ) lam) (hq : q ∈ Ioc lam 1) :
    (phi x * (q + B + rankPotential phi lam x q - lam) ≤ max (-phi q) 0 * c) ↔
      B + (lowRankRatio phi lam x - correctionRatio phi c x) * (-phi q) ≤ 0 := by
  have hp : 0 < phi x := h.positive hx
  have hneg := h.nonpositive ⟨hq.1.le, hq.2⟩
  rw [max_eq_left (neg_nonneg.mpr hneg)]
  have hid : phi x * (q + B + rankPotential phi lam x q - lam) - (-phi q) * c =
      phi x * (B + (lowRankRatio phi lam x - correctionRatio phi c x) * (-phi q)) := by
    simp only [rankPotential, if_neg (not_le.mpr hq.1), lowRankRatio, correctionRatio]
    field_simp
    ring
  constructor
  · intro hh
    apply nonpos_of_mul_nonpos_right (a := phi x) _ hp
    rw [← hid]
    linarith
  · intro hh
    have hm := mul_nonpos_of_nonneg_of_nonpos hp.le hh
    rw [← hid] at hm
    linarith

theorem normalized_high_second_low {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    {x q z B c : ℝ} (hx : x ∈ Ico (0 : ℝ) lam)
    (hq : q ∈ Icc (0 : ℝ) lam) (hz : z ∈ Icc (0 : ℝ) lam) :
    (phi x * (q + B + rankPotential phi lam x q - rankPotential phi lam x z) ≤ max (-phi z) 0 * c) ↔
      q + B ≤ 0 := by
  rw [rankPotential_low phi lam x q hq.2, rankPotential_low phi lam x z hz.2,
    max_eq_right (neg_nonpos.mpr (h.nonnegative hz)), zero_mul, add_zero, sub_zero]
  constructor
  · intro hh; exact nonpos_of_mul_nonpos_right hh (h.positive hx)
  · intro hh; exact mul_nonpos_of_nonneg_of_nonpos (h.positive hx).le hh

theorem normalized_high_second_mixed {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    {x q z B c : ℝ} (hx : x ∈ Ico (0 : ℝ) lam)
    (hq : q ≤ lam) (hz : z ∈ Ioc lam 1) :
    (phi x * (q + B + rankPotential phi lam x q - rankPotential phi lam x z) ≤ max (-phi z) 0 * c) ↔
      z + q - lam + B + (lowRankRatio phi lam x + correctionRatio phi c x) * phi z ≤ 0 := by
  have hp : 0 < phi x := h.positive hx
  have hneg := h.nonpositive ⟨hz.1.le, hz.2⟩
  rw [max_eq_left (neg_nonneg.mpr hneg)]
  have hid : phi x * (q + B + rankPotential phi lam x q - rankPotential phi lam x z) - (-phi z) * c =
      phi x * (z + q - lam + B + (lowRankRatio phi lam x + correctionRatio phi c x) * phi z) := by
    rw [rankPotential_low phi lam x q hq]
    simp only [rankPotential, if_neg (not_le.mpr hz.1), lowRankRatio, correctionRatio]
    field_simp
    ring
  constructor
  · intro hh
    apply nonpos_of_mul_nonpos_right (a := phi x) _ hp
    rw [← hid]; linarith
  · intro hh
    have hm := mul_nonpos_of_nonneg_of_nonpos hp.le hh
    rw [← hid] at hm
    linarith

theorem normalized_high_second_high {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    {x q z B c : ℝ} (hx : x ∈ Ico (0 : ℝ) lam)
    (hq : lam < q) (hz : z ∈ Ioc lam 1) :
    (phi x * (q + B + rankPotential phi lam x q - rankPotential phi lam x z) ≤ max (-phi z) 0 * c) ↔
      z + B - lowRankRatio phi lam x * (phi q - phi z) + correctionRatio phi c x * phi z ≤ 0 := by
  have hp : 0 < phi x := h.positive hx
  have hneg := h.nonpositive ⟨hz.1.le, hz.2⟩
  rw [max_eq_left (neg_nonneg.mpr hneg)]
  have hid : phi x * (q + B + rankPotential phi lam x q - rankPotential phi lam x z) - (-phi z) * c =
      phi x * (z + B - lowRankRatio phi lam x * (phi q - phi z) + correctionRatio phi c x * phi z) := by
    simp only [rankPotential, if_neg (not_le.mpr hq), if_neg (not_le.mpr hz.1), lowRankRatio, correctionRatio]
    field_simp
    ring
  constructor
  · intro hh
    apply nonpos_of_mul_nonpos_right (a := phi x) _ hp
    rw [← hid]; linarith
  · intro hh
    have hm := mul_nonpos_of_nonneg_of_nonpos hp.le hh
    rw [← hid] at hm
    linarith

end OptimalG
