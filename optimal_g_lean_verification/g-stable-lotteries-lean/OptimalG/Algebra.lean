import Mathlib.Tactic

/-!
# Exact algebra in Elections 2--3 and Section 5.2

These results verify the displayed algebra with explicit hypotheses. They do not assume or prove
the existence of an optimal activation, the variational minimizer, or any numerical certificate.
The variables `fx`, `fy`, and `fz` stand for the three values of the centered activation.
-/

namespace OptimalG

def weightOne (R K fy fz : ℝ) : ℝ := -K * fy - R * fz
def weightTwo (R P fx fy : ℝ) : ℝ := R * fx + P * fy
def weightThree (P K fx fz : ℝ) : ℝ := K * fx - P * fz
def determinant (lam p x y R P : ℝ) : ℝ :=
  (2 * lam - x) * R - (p + y - lam) * P

/-- The supported-class activation balances for the minors in (3.6). -/
theorem minors_balance_class (R P K fx fy fz : ℝ) :
    P * weightOne R K fy fz + K * weightTwo R P fx fy -
      R * weightThree P K fx fz = 0 := by
  unfold weightOne weightTwo weightThree
  ring

/-- The unsupported optimal candidate's activation balances too. -/
theorem minors_balance_optimum (R P K fx fy fz : ℝ) :
    -fx * weightOne R K fy fz - fz * weightTwo R P fx fy -
      fy * weightThree P K fx fz = 0 := by
  unfold weightOne weightTwo weightThree
  ring

/-- Expanding the weighted excess social cost gives exactly (3.7). -/
theorem election_three_expansion (lam p x y z R P K fx fy fz : ℝ) :
    -(2 * lam - x) * weightOne R K fy fz +
      (z - lam) * weightTwo R P fx fy +
      (p + y - lam) * weightThree P K fx fz =
    ((z - lam) * R + (p + y - lam) * K) * fx +
      ((z - lam) * P + (2 * lam - x) * K) * fy +
      determinant lam p x y R P * fz := by
  unfold weightOne weightTwo weightThree determinant
  ring

/-- Election 2: its positive-denominator ratio bound is precisely (3.4). -/
theorem election_two_ratio_iff (lam p q R delta : ℝ) (hR : 0 < R) :
    q + p * delta / R ≤ lam ↔ p * delta ≤ (lam - q) * R := by
  rw [← le_sub_iff_add_le', div_le_iff₀ hR]

/-- The nonpositive-delta case of (3.4) does not require a constructed election. -/
theorem election_two_nonpositive (lam p q R delta : ℝ)
    (hp : 0 ≤ p) (hR : 0 ≤ R) (hq : q ≤ lam) (hd : delta ≤ 0) :
    p * delta ≤ (lam - q) * R := by
  exact le_trans (mul_nonpos_of_nonneg_of_nonpos hp hd)
    (mul_nonneg (sub_nonneg.mpr hq) hR)

/-- First supporting-line cancellation on manuscript page 18. -/
theorem support_identity_one (lam p x y R P beta eta fx fy : ℝ)
    (hx : eta * fx = 2 * lam - x - beta * P)
    (hy : eta * fy = lam - p - y + beta * R) :
    eta * (R * fx + P * fy) = determinant lam p x y R P := by
  calc
    _ = R * (eta * fx) + P * (eta * fy) := by ring
    _ = determinant lam p x y R P := by rw [hx, hy]; unfold determinant; ring

/-- Second supporting-line cancellation on manuscript page 18. -/
theorem support_identity_two (lam p x y R P beta eta fx fy : ℝ)
    (hx : eta * fx = 2 * lam - x - beta * P)
    (hy : eta * fy = lam - p - y + beta * R) :
    eta * ((p + y - lam) * fx + (2 * lam - x) * fy) =
      beta * determinant lam p x y R P := by
  calc
    _ = (p + y - lam) * (eta * fx) + (2 * lam - x) * (eta * fy) := by ring
    _ = beta * determinant lam p x y R P := by
      rw [hx, hy]; unfold determinant; ring

/-- The precise bridge from Election 3 to verifier inequality (5.13).
The supporting equalities and positivity of the determinant are explicit premises;
their existence is a separate analytic obligation. -/
theorem election_three_implies_high_verifier
    (lam p x y z R P K beta eta fx fy fz : ℝ)
    (heta : 0 < eta) (hdet : 0 < determinant lam p x y R P)
    (hx : eta * fx = 2 * lam - x - beta * P)
    (hy : eta * fy = lam - p - y + beta * R)
    (helection :
      ((z - lam) * R + (p + y - lam) * K) * fx +
        ((z - lam) * P + (2 * lam - x) * K) * fy +
        determinant lam p x y R P * fz ≤ 0) :
    z - lam + beta * K + eta * fz ≤ 0 := by
  have h1 := support_identity_one lam p x y R P beta eta fx fy hx hy
  have h2 := support_identity_two lam p x y R P beta eta fx fy hx hy
  have factor : eta *
      (((z - lam) * R + (p + y - lam) * K) * fx +
        ((z - lam) * P + (2 * lam - x) * K) * fy +
        determinant lam p x y R P * fz) =
      determinant lam p x y R P * (z - lam + beta * K + eta * fz) := by
    calc
      _ = (z - lam) * (eta * (R * fx + P * fy)) +
          K * (eta * ((p + y - lam) * fx + (2 * lam - x) * fy)) +
          determinant lam p x y R P * (eta * fz) := by ring
      _ = _ := by rw [h1, h2]; ring
  have h := mul_nonpos_of_nonneg_of_nonpos (le_of_lt heta) helection
  rw [factor] at h
  nlinarith

def correction (lam eta x fx : ℝ) : ℝ := max (eta * fx - (lam - x)) 0

theorem correction_nonnegative (lam eta x fx : ℝ) :
    0 ≤ correction lam eta x fx := le_max_right _ _

/-- The smallest nonnegative correction majorizes the required affine correction. -/
theorem correction_coefficient (lam eta x fx : ℝ) (hfx : 0 < fx) :
    eta ≤ (lam - x + correction lam eta x fx) / fx := by
  apply (le_div_iff₀ hfx).mpr
  have h := le_max_left (eta * fx - (lam - x)) 0
  dsimp [correction]
  linarith

/-- The q=0 low-rank inequality, including the zero-correction case. -/
theorem correction_low_top (lam eta x fx beta P : ℝ)
    (hbase : beta * P ≤ lam)
    (hsupport : x + beta * P + eta * fx ≤ 2 * lam) :
    beta * P + correction lam eta x fx ≤ lam := by
  unfold correction
  rcases le_total 0 (eta * fx - (lam - x)) with h | h
  · rw [max_eq_left h]; linarith
  · rw [max_eq_right h]; linarith

/-- The q=p low-rank inequality, including the zero-correction case. -/
theorem correction_low_bottom (lam eta y fy beta R p : ℝ)
    (hbase : p ≤ beta * R)
    (hsupport : y + p - beta * R + eta * fy ≤ lam) :
    p - beta * R + correction lam eta y fy ≤ 0 := by
  unfold correction
  rcases le_total 0 (eta * fy - (lam - y)) with h | h
  · rw [max_eq_left h]; linarith
  · rw [max_eq_right h]; linarith

/-- (5.13) implies the q=0 high-rank verifier inequality for any low rank x. -/
theorem correction_high (lam eta x z fx fz beta K : ℝ)
    (hfx : 0 < fx) (hfz : fz ≤ 0)
    (hhigh : z - lam + beta * K + eta * fz ≤ 0) :
    z - lam + beta * K +
      ((lam - x + correction lam eta x fx) / fx) * fz ≤ 0 := by
  have hc := correction_coefficient lam eta x fx hfx
  have hm := mul_le_mul_of_nonpos_right hc hfz
  linarith

/-- Exact rational consequence of the numerical interval, *conditional* on that interval. -/
theorem distortion_interval_of_lambda_interval (lam : ℝ)
    (hlo : (56232844 : ℝ) / 100000000 < lam)
    (hhi : lam < (56232847 : ℝ) / 100000000) :
    (212465688 : ℝ) / 100000000 < 1 + 2 * lam ∧
      1 + 2 * lam < (212465694 : ℝ) / 100000000 := by
  constructor <;> linarith

end OptimalG
