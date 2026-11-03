import OptimalG.VariationalPrimitive

/-!
# Coarse analytic domain bounds

These bounds are proved from the variational constraints. They are deliberately
weaker than the sharp certificate bounds in Appendix D, but already give a
uniformly positive denominator in (4.2).
-/

namespace OptimalG.Variational

open Set

theorem cap_lower_on_initial_interval (lam S r : ℝ)
    (hlam : lam ∈ Icc lambdaLo lambdaHi)
    (hS : (21972 : ℝ) / 1000000 ≤ S)
    (hr : r ∈ Icc pLo ell) :
    quadratic lam r - S ≤ cap lam S r := by
  have hlo := hlam.1
  have hhi := hlam.2
  have hrlo := hr.1
  have hrhi := hr.2
  norm_num [lambdaLo, lambdaHi, pLo, ell] at hlo hhi hrlo hrhi
  let F : ℝ := lam ^ 2 - lam / 2 - lam * r / 2 + r ^ 2 / 2
  have hF : -(4478594375 : ℝ) / 1000000000000 ≤ F := by
    have h1 := mul_nonneg (show 0 ≤ lam - (562325 : ℝ) / 1000000 by linarith)
      (show 0 ≤ lam + (562325 : ℝ) / 1000000 - 1 / 2 - r / 2 by linarith)
    have h2 := mul_nonneg (show 0 ≤ (28 : ℝ) / 100 - r by linarith)
      (show 0 ≤ (562325 : ℝ) / 1000000 - r - (28 : ℝ) / 100 by linarith)
    dsimp [F]
    nlinarith
  have ht : 0 < 1 - r := by linarith
  have hc : 0 ≤ 1 - r - lam := by linarith
  have hm := mul_nonneg ht.le (sub_nonneg.mpr hF)
  have hs := mul_nonneg (sub_nonneg.mpr hS) hc
  have hnum : 0 ≤ (1 - r) * F + S * (1 - r - lam) := by
    nlinarith
  have hid : (1 - r) * (cap lam S r - (quadratic lam r - S)) =
      (1 - r) * F + S * (1 - r - lam) := by
    dsimp [cap, quadratic, F]
    field_simp
    ring
  have hprod : 0 ≤ (1 - r) * (cap lam S r - (quadratic lam r - S)) := by
    rw [hid]
    exact hnum
  have := (mul_nonneg_iff_of_pos_left ht).mp hprod
  linarith

theorem Admissible.primitive_lower {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {r : ℝ} (hr : r ∈ Icc pLo zStart) :
    quadratic lam r - d.S ≤ primitive lam d r := by
  unfold primitive
  split_ifs with hrell hrend
  · exact cap_lower_on_initial_interval lam d.S r h.1 h.slack_lower ⟨hr.1, hrell⟩
  · exact h.lowPrimitive_lower ⟨le_of_lt (lt_of_not_ge hrell), hrend⟩
  · exact le_rfl

theorem Admissible.control_R_lower {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {p : ℝ} (hp : p ∈ Icc pLo pHi) :
    (826 : ℝ) / 10000 ≤ primitive lam d p := by
  have hS := h.slack_upper
  have hlo := h.1.1
  have hp0 := hp.1
  have hp1 := hp.2
  have hpz : p ≤ zStart := by norm_num [pHi, zStart] at hp1 ⊢; linarith
  have hJ := h.primitive_lower ⟨hp.1, hpz⟩
  norm_num [lambdaLo, pLo, pHi] at hlo hp0 hp1
  have hprod := mul_nonneg (show 0 ≤ p - 1 / 4 by linarith)
    (show 0 ≤ lam - (p + 1 / 4) / 2 by linarith)
  dsimp [quadratic] at hJ
  nlinarith

theorem Admissible.control_P_bounds {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {p : ℝ} (hp : p ∈ Icc pLo pHi) :
    0 ≤ quadratic lam (1 - p) - d.S ∧
      quadratic lam (1 - p) - d.S ≤ (159 : ℝ) / 1000 := by
  have hSlo := h.slack_lower
  have hShi := h.slack_upper
  have hlo := h.1.1
  have hhi := h.1.2
  have hp0 := hp.1
  have hp1 := hp.2
  norm_num [lambdaLo, lambdaHi, pLo, pHi] at hlo hhi hp0 hp1
  have hprod := mul_nonneg (show 0 ≤ p - 1 / 4 by linarith)
    (show 0 ≤ (1 - p) + 3 / 4 - 2 * lam by linarith)
  have hlam2 := mul_nonneg (show 0 ≤ (562330 : ℝ) / 1000000 - lam by linarith)
    (show 0 ≤ (562330 : ℝ) / 1000000 + lam by linarith)
  dsimp [quadratic]
  constructor
  · nlinarith
  · nlinarith [sq_nonneg (1 - p - lam)]

/-- A direct, coarse uniform bound. The stronger .0519 bound in the manuscript
is unnecessary for mere nonvanishing and Lipschitz existence. -/
theorem Admissible.determinant_positive {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {c : Control} (hc : c ∈ controlDomain) :
    (3 : ℝ) / 100 < controlDeterminant lam d c := by
  have hR := h.control_R_lower hc.1
  have hP := h.control_P_bounds hc.1
  have hlo := h.1.1
  have hx := hc.2.1.2
  have hp := hc.1.2
  have hy := hc.2.2.2
  norm_num [lambdaLo, xHi, pHi] at hlo hx hp hy
  let R := primitive lam d c.1
  let P := quadratic lam (1 - c.1) - d.S
  have hcoef : (74465 : ℝ) / 100000 ≤ 2 * lam - c.2.1 := by linarith
  have hk : c.1 + c.2.2 - lam ≤ (177675 : ℝ) / 1000000 := by linarith
  have hmR := mul_nonneg
    (show 0 ≤ 2 * lam - c.2.1 - (74465 : ℝ) / 100000 by linarith)
    (show 0 ≤ R by dsimp [R]; linarith)
  have hmP := mul_nonneg
    (show 0 ≤ (177675 : ℝ) / 1000000 - (c.1 + c.2.2 - lam) by linarith)
    hP.1
  dsimp [controlDeterminant]
  dsimp [R] at hmR
  nlinarith [hP.2]

/-- An elementary upper bound on the low-rank primitive, sufficient for
boundedness of the control coefficients. -/
theorem Admissible.control_R_upper {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {p : ℝ} (hp : p ∈ Icc pLo pHi) :
    primitive lam d p ≤ 2 := by
  have hcap : primitive lam d p ≤ cap lam d.S p := by
    unfold primitive
    split_ifs with he ht
    · exact le_rfl
    · exact h.lowPrimitive_le_cap ⟨le_of_lt (lt_of_not_ge he), ht⟩
    · have := hp.2
      norm_num [pHi, tEnd] at this ht
      linarith
  have hlo := h.1.1
  have hhi := h.1.2
  have hS := h.slack_lower
  have hp0 := hp.1
  have hp1 := hp.2
  norm_num [lambdaLo, lambdaHi, pLo, pHi] at hlo hhi hp0 hp1
  have hfrac : 0 ≤ lam * d.S / (1 - p) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hlam2 := mul_nonneg (show 0 ≤ 1 - lam by linarith)
    (show 0 ≤ 1 + lam by linarith)
  have hlamp := mul_nonneg (show 0 ≤ lam by linarith)
    (show 0 ≤ 1 - p by linarith)
  dsimp [cap] at hcap
  nlinarith

end OptimalG.Variational
