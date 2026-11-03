import OptimalG.Certificates.Control

/-! Sign-complete algebra for Election 3, after actual finite election tests. -/
namespace OptimalG
open Certificates.Control

/-- Balanced nonnegative weights satisfying reference stability obey the
necessary metric excess bound. This is the precise interface supplied by the
finite-to-real Election 3 construction. -/
def ThreeClassWeightTest (R P K A B C h U k : ℝ) : Prop :=
  ∀ w1 w2 w3 : ℝ, 0 ≤ w1 → 0 ≤ w2 → 0 ≤ w3 →
    P * w1 + K * w2 - R * w3 = 0 → 0 ≤ A * w1 + C * w2 + B * w3 →
    -h * w1 + U * w2 + k * w3 ≤ 0

/-- The minor argument includes every sign case, rather than assuming that
its three proposed voter weights are positive. -/
theorem three_class_minors_nonpos {R P K A B C h U k : ℝ}
    (hR : 0 < R) (hP : 0 < P) (hK : 0 < K)
    (hD : 0 < h * R - k * P) (hX : 0 < U * R + k * K)
    (htest : ThreeClassWeightTest R P K A B C h U k) :
    (U * R + k * K) * A + (U * P + h * K) * B + (h * R - k * P) * C ≤ 0 := by
  let w1 := -K * B - R * C
  let w2 := R * A + P * B
  let w3 := K * A - P * C
  have hbalance : P * w1 + K * w2 - R * w3 = 0 := by dsimp [w1, w2, w3]; ring
  have hreference : A * w1 + C * w2 + B * w3 = 0 := by dsimp [w1, w2, w3]; ring
  have hw1 : 0 < w1 := by
    by_contra! hn
    have hh := htest 0 R K (by norm_num) hR.le hK.le (by ring)
      (by dsimp [w1] at hn; nlinarith)
    nlinarith
  have heq : (U * R + k * K) * A + (U * P + h * K) * B + (h * R - k * P) * C =
      -h * w1 + U * w2 + k * w3 := by dsimp [w1, w2, w3]; ring
  rw [heq]
  by_cases hw2 : w2 ≤ 0
  · have hfirst := mul_neg_of_neg_of_pos (neg_neg_of_pos hD) hw1
    have hsecond := mul_nonpos_of_nonneg_of_nonpos hX.le hw2
    have hid : R * (-h * w1 + U * w2 + k * w3) =
        -(h * R - k * P) * w1 + (U * R + k * K) * w2 := by
      nlinarith [hbalance]
    have hh : R * (-h * w1 + U * w2 + k * w3) < 0 := by rw [hid]; linarith
    exact (neg_of_mul_neg_right hh hR.le).le
  · have hw2pos : 0 < w2 := lt_of_not_ge hw2
    have hw3 : 0 < w3 := by
      have h1 := mul_pos hP hw1
      have h2 := mul_pos hK hw2pos
      nlinarith
    exact htest w1 w2 w3 hw1.le hw2pos.le hw3.le hbalance (by rw [hreference])

/-- Positive primitives and the opposite binary test force the determinant
positive on the full Election 3 domain, including negative k. -/
theorem three_class_determinant_positive {L p x y R P : ℝ}
    (hL : 0 < L) (hp : 0 < p) (hx : x < L) (hy : y < L)
    (hR : 0 < R) (hP : 0 < P) (hbinary : p * P ≤ L * R) :
    0 < (2 * L - x) * R - (p + y - L) * P := by
  have hh : 0 < 2 * L - x := by linarith
  by_cases hk : 0 ≤ p + y - L
  · have hb := mul_le_mul_of_nonneg_left hbinary hk
    have hp1 := mul_pos (mul_pos hp (sub_pos.mpr hx)) hR
    have hp2 := mul_pos (mul_pos hL (sub_pos.mpr hy)) hR
    have hdet : 0 < p * ((2 * L - x) * R - (p + y - L) * P) := by nlinarith
    exact pos_of_mul_pos_right hdet hp.le
  · have hneg := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hk) hP.le
    have hpos := mul_pos hh hR
    linarith

end OptimalG
