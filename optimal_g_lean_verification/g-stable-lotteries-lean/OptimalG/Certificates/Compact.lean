import OptimalG.Certificates.Slater
import OptimalG.Certificates.GeneratedCompact
import OptimalG.Algebra

/-!
# Kernel-checked compact-domain numerical inequalities

These are inequalities of the actual functions Q and C, over real rectangles.
Generated rational box trees are accepted by ordinary kernel reduction.
The corrected low-rank average is between 0.09 and 0.13, disproving the
manuscript's printed bound 0.18 while retaining the margin needed in B.1.
-/

namespace OptimalG.Certificates.Compact

noncomputable def scalarLower : ℝ := 28711863873 / 1306700000000
noncomputable def scalarUpper : ℝ := 0.0266503148804352

def LambdaRange (L : ℝ) : Prop := L ∈ Set.Icc (0.562325 : ℝ) 0.562330
def ScalarRange (S : ℝ) : Prop := S ∈ Set.Icc scalarLower scalarUpper

noncomputable def binaryGap (L S p : ℝ) : ℝ :=
  L * (quadratic L p - S) - p * (quadratic L (1 - p) - S)

noncomputable def determinantLower (L S p : ℝ) : ℝ :=
  (2 * L - 0.38) * (quadratic L p - S) -
    (p + 0.38 - L) * (quadratic L (1 - p) - S)

noncomputable def terminalBarrier (L S z q : ℝ) : ℝ :=
  z * (quadratic L (1 - z + q) - S - cap L S q) / (L - q)

noncomputable def rootBudget (L z : ℝ) : ℝ := quadratic L z - quadratic L 1

noncomputable def lowAverage (L S : ℝ) : ℝ :=
  (quadratic L 0.38 - S - cap L S 0.36) / 0.02

private theorem vec3_last (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 2 = c := rfl

private theorem opposite_eval (L S p : ℝ) :
    GeneratedCompact.oppositeExpr.eval ![L, S, p] = binaryGap L S p := by
  norm_num [GeneratedCompact.oppositeExpr, RatExpr.eval, vec3_last, binaryGap, quadratic, div_eq_mul_inv]
  ring

private theorem determinant_eval (L S p : ℝ) :
    GeneratedCompact.determinantExpr.eval ![L, S, p] = determinantLower L S p := by
  norm_num [GeneratedCompact.determinantExpr, RatExpr.eval, vec3_last, determinantLower, quadratic, div_eq_mul_inv]
  ring

private theorem root_budget_eval (L S z : ℝ) :
    GeneratedCompact.root_budgetExpr.eval ![L, S, z] =
      terminalBarrier L S z 0.27 - rootBudget L z := by
  norm_num [GeneratedCompact.root_budgetExpr, RatExpr.eval, vec3_last, terminalBarrier, rootBudget,
    quadratic, cap, div_eq_mul_inv]
  ring

private theorem average_eval (L S : ℝ) :
    GeneratedCompact.average38Expr.eval ![L, S, 0] = lowAverage L S := by
  norm_num [GeneratedCompact.average38Expr, RatExpr.eval, vec3_last, lowAverage, quadratic, cap, div_eq_mul_inv]
  ring

private theorem average_upper_eval (L S : ℝ) :
    GeneratedCompact.average38_upperExpr.eval ![L, S, 0] = -lowAverage L S := by
  norm_num [GeneratedCompact.average38_upperExpr, RatExpr.eval, vec3_last, lowAverage, quadratic, cap,
    div_eq_mul_inv]
  ring

theorem binary_gap_gt (L S p : ℝ) (hL : LambdaRange L) (hS : ScalarRange S)
    (hp : p ∈ Set.Icc (0.25 : ℝ) 0.36) : 0.01446 < binaryGap L S p := by
  have hx : ∀ i, (GeneratedCompact.oppositeDomain i).Contains (![L, S, p] i) := by
    intro i
    fin_cases i <;>
      norm_num [GeneratedCompact.oppositeDomain, RatInterval.Contains,
        LambdaRange, ScalarRange, scalarLower, scalarUpper] at *
    · exact hL
    · exact hS
    · exact hp
  have h := BoxCertificate.checkLower_sound GeneratedCompact.oppositeExpr (723 / 50000)
    GeneratedCompact.oppositeCertificate GeneratedCompact.oppositeDomain
    GeneratedCompact.opposite_checked ![L, S, p] hx
  rw [opposite_eval] at h
  norm_num at h ⊢
  exact h

theorem determinant_lower_gt (L S p : ℝ) (hL : LambdaRange L) (hS : ScalarRange S)
    (hp : p ∈ Set.Icc (0.25 : ℝ) 0.36) : 0.0519 < determinantLower L S p := by
  have hx : ∀ i, (GeneratedCompact.determinantDomain i).Contains (![L, S, p] i) := by
    intro i
    fin_cases i <;>
      norm_num [GeneratedCompact.determinantDomain, RatInterval.Contains,
        LambdaRange, ScalarRange, scalarLower, scalarUpper] at *
    · exact hL
    · exact hS
    · exact hp
  have h := BoxCertificate.checkLower_sound GeneratedCompact.determinantExpr (519 / 10000)
    GeneratedCompact.determinantCertificate GeneratedCompact.determinantDomain
    GeneratedCompact.determinant_checked ![L, S, p] hx
  rw [determinant_eval] at h
  norm_num at h ⊢
  exact h

theorem terminal_above_root_budget (L S z : ℝ) (hL : LambdaRange L) (hS : ScalarRange S)
    (hz : z ∈ Set.Icc (0.775 : ℝ) 0.875) :
    0.019 < terminalBarrier L S z 0.27 - rootBudget L z := by
  have hx : ∀ i, (GeneratedCompact.root_budgetDomain i).Contains (![L, S, z] i) := by
    intro i
    fin_cases i <;>
      norm_num [GeneratedCompact.root_budgetDomain, RatInterval.Contains,
        LambdaRange, ScalarRange, scalarLower, scalarUpper] at *
    · exact hL
    · exact hS
    · exact hz
  have h := BoxCertificate.checkLower_sound GeneratedCompact.root_budgetExpr (19 / 1000)
    GeneratedCompact.root_budgetCertificate GeneratedCompact.root_budgetDomain
    GeneratedCompact.root_budget_checked ![L, S, z] hx
  rw [root_budget_eval] at h
  norm_num at h ⊢
  exact h

theorem low_average_gt (L S : ℝ) (hL : LambdaRange L) (hS : ScalarRange S) :
    0.09 < lowAverage L S := by
  have hx : ∀ i, (GeneratedCompact.average38Domain i).Contains (![L, S, 0] i) := by
    intro i
    fin_cases i <;>
      norm_num [GeneratedCompact.average38Domain, RatInterval.Contains,
        LambdaRange, ScalarRange, scalarLower, scalarUpper] at *
    · exact hL
    · exact hS
  have h := BoxCertificate.checkLower_sound GeneratedCompact.average38Expr (9 / 100)
    GeneratedCompact.average38Certificate GeneratedCompact.average38Domain
    GeneratedCompact.average38_checked ![L, S, 0] hx
  rw [average_eval] at h
  norm_num at h ⊢
  exact h

theorem low_average_lt (L S : ℝ) (hL : LambdaRange L) (hS : ScalarRange S) :
    lowAverage L S < 0.13 := by
  have hx : ∀ i, (GeneratedCompact.average38_upperDomain i).Contains (![L, S, 0] i) := by
    intro i
    fin_cases i <;>
      norm_num [GeneratedCompact.average38_upperDomain, RatInterval.Contains,
        LambdaRange, ScalarRange, scalarLower, scalarUpper] at *
    · exact hL
    · exact hS
  have h := BoxCertificate.checkLower_sound GeneratedCompact.average38_upperExpr (-13 / 100)
    GeneratedCompact.average38_upperCertificate GeneratedCompact.average38_upperDomain
    GeneratedCompact.average38_upper_checked ![L, S, 0] hx
  rw [average_upper_eval] at h
  norm_num at h ⊢
  linarith

/-- The 0.18 claim on printed page 49 is incompatible with every point of the
stated compact scalar rectangle. The replacement 0.09 is sufficient for B.1. -/
theorem printed_average_bound_false (L S : ℝ) (hL : LambdaRange L) (hS : ScalarRange S) :
    ¬ (0.18 < lowAverage L S) := by
  have h := low_average_lt L S hL hS
  linarith

theorem corrected_average_suffices (L S : ℝ) (hL : LambdaRange L) (hS : ScalarRange S) :
    0 < lowAverage L S - 0.60 * (0.38 - 0.285) := by
  have h := low_average_gt L S hL hS
  linarith

/-- Endpoint separation used to splice the monotone envelope back to Q−S. -/
theorem endpoint38_gap (L S : ℝ) (hL : LambdaRange L) (hS : ScalarRange S) :
    0.0199 < quadratic L 0.38 - S - cap L S 0.28 := by
  have hx : ∀ i, (GeneratedCompact.endpoint38Domain i).Contains (![L, S, 0] i) := by
    intro i
    fin_cases i <;>
      norm_num [GeneratedCompact.endpoint38Domain, RatInterval.Contains,
        LambdaRange, ScalarRange, scalarLower, scalarUpper] at *
    · exact hL
    · exact hS
  have h := BoxCertificate.checkLower_sound GeneratedCompact.endpoint38Expr (199 / 10000)
    GeneratedCompact.endpoint38Certificate GeneratedCompact.endpoint38Domain
    GeneratedCompact.endpoint38_checked ![L, S, 0] hx
  have he : GeneratedCompact.endpoint38Expr.eval ![L, S, 0] =
      quadratic L 0.38 - S - cap L S 0.28 := by
    norm_num [GeneratedCompact.endpoint38Expr, RatExpr.eval, quadratic, cap, div_eq_mul_inv]
    ring
  rw [he] at h
  norm_num at h ⊢
  exact h

theorem endpoint385_gap (L S : ℝ) (hL : LambdaRange L) (hS : ScalarRange S) :
    0.0227 < quadratic L 0.385 - S - cap L S 0.28 := by
  have hx : ∀ i, (GeneratedCompact.endpoint385Domain i).Contains (![L, S, 0] i) := by
    intro i
    fin_cases i <;>
      norm_num [GeneratedCompact.endpoint385Domain, RatInterval.Contains,
        LambdaRange, ScalarRange, scalarLower, scalarUpper] at *
    · exact hL
    · exact hS
  have h := BoxCertificate.checkLower_sound GeneratedCompact.endpoint385Expr (227 / 10000)
    GeneratedCompact.endpoint385Certificate GeneratedCompact.endpoint385Domain
    GeneratedCompact.endpoint385_checked ![L, S, 0] hx
  have he : GeneratedCompact.endpoint385Expr.eval ![L, S, 0] =
      quadratic L 0.385 - S - cap L S 0.28 := by
    norm_num [GeneratedCompact.endpoint385Expr, RatExpr.eval, quadratic, cap, div_eq_mul_inv]
    ring
  rw [he] at h
  norm_num at h ⊢
  exact h

/-- Absolute value of the scalar slope of the terminal binary barrier. -/
theorem barrier_scalar_slope_bound (L q z : ℝ) (hL : LambdaRange L)
    (hq : q ∈ Set.Icc (0.26 : ℝ) 0.28) (hz : z ∈ Set.Icc (0.84 : ℝ) 0.875) :
    z * (1 - q - L) / ((L - q) * (1 - q)) < 0.765 := by
  have hx : ∀ i, (GeneratedCompact.scalar_derivativeDomain i).Contains (![L, q, z] i) := by
    intro i
    fin_cases i <;>
      norm_num [GeneratedCompact.scalar_derivativeDomain, RatInterval.Contains, LambdaRange] at *
    · exact hL
    · exact hq
    · exact hz
  have h := BoxCertificate.checkLower_sound GeneratedCompact.scalar_derivativeExpr (0 / 1)
    GeneratedCompact.scalar_derivativeCertificate GeneratedCompact.scalar_derivativeDomain
    GeneratedCompact.scalar_derivative_checked ![L, q, z] hx
  have he : GeneratedCompact.scalar_derivativeExpr.eval ![L, q, z] =
      0.765 - z * (1 - q - L) / ((L - q) * (1 - q)) := by
    norm_num [GeneratedCompact.scalar_derivativeExpr, RatExpr.eval, vec3_last, div_eq_mul_inv]
    ring
  rw [he] at h
  norm_num at h
  linarith

theorem low_primitive_floor (L S p : ℝ) (hL : LambdaRange L) (hS : ScalarRange S)
    (hp : p ∈ Set.Icc (0.25 : ℝ) 0.36) : 0.0826 < quadratic L p - S := by
  have hf : 0 ≤ L - (p + 0.25) / 2 := by linarith [hL.1, hp.2]
  have hh := mul_nonneg (sub_nonneg.mpr hp.1) hf
  have hs := hS.2
  norm_num [scalarUpper] at hs
  unfold quadratic
  nlinarith [hL.1]

theorem complementary_primitive_floor (L S p : ℝ) (hL : LambdaRange L) (hS : ScalarRange S)
    (hp : p ∈ Set.Icc (0.25 : ℝ) 0.36) : 0.113 < quadratic L (1 - p) - S := by
  have hf : 0 ≤ (1.75 - p) / 2 - L := by linarith [hL.2, hp.2]
  have hh := mul_nonneg (sub_nonneg.mpr hp.1) hf
  have hs := hS.2
  norm_num [scalarUpper] at hs
  unfold quadratic
  nlinarith [hL.1]

/-- The strict opposite-binary inequality for any admissible low primitive R. -/
theorem opposite_binary_gt (L S p R : ℝ) (hL : LambdaRange L) (hS : ScalarRange S)
    (hp : p ∈ Set.Icc (0.25 : ℝ) 0.36) (hR : quadratic L p - S ≤ R) :
    0.01446 < L * R - p * (quadratic L (1 - p) - S) := by
  have hb := binary_gap_gt L S p hL hS hp
  have hm := mul_le_mul_of_nonneg_left hR (show 0 ≤ L by linarith [hL.1])
  unfold binaryGap at hb
  linarith

/-- The actual determinant in Election 3 is uniformly separated from zero. -/
theorem determinant_gt (L S p x y R : ℝ) (hL : LambdaRange L) (hS : ScalarRange S)
    (hp : p ∈ Set.Icc (0.25 : ℝ) 0.36) (hx : x ≤ 0.38) (hy : y ≤ 0.38)
    (hR : quadratic L p - S ≤ R) :
    0.0519 < OptimalG.determinant L p x y R (quadratic L (1 - p) - S) := by
  have hb := determinant_lower_gt L S p hL hS hp
  have hr0 : 0 ≤ R := by linarith [low_primitive_floor L S p hL hS hp]
  have hp0 : 0 ≤ quadratic L (1 - p) - S := by
    linarith [complementary_primitive_floor L S p hL hS hp]
  have hh : 0 ≤ 2 * L - 0.38 := by linarith [hL.1]
  have hm := mul_le_mul_of_nonneg_left hR hh
  have hxm := mul_nonneg (sub_nonneg.mpr hx) hr0
  have hym := mul_nonneg (sub_nonneg.mpr hy) hp0
  unfold determinantLower at hb
  unfold OptimalG.determinant
  nlinarith

/-- All complementary ranks in the necessary-family domain lie in the plateau. -/
theorem complementary_rank_ranges (p z zT q : ℝ)
    (hp : p ∈ Set.Icc (0.25 : ℝ) 0.36)
    (hz : z ∈ Set.Icc (0.775 : ℝ) 0.875)
    (hzT : zT ∈ Set.Icc (0.84 : ℝ) 0.875)
    (hq : q ∈ Set.Icc (0.26 : ℝ) 0.28) :
    1 - p ∈ Set.Icc (0.64 : ℝ) 0.75 ∧
    z - p ∈ Set.Icc (0.415 : ℝ) 0.625 ∧
    1 - zT + q ∈ Set.Icc (0.385 : ℝ) 0.44 := by
  rcases hp with ⟨hpl, hpu⟩
  rcases hz with ⟨hzl, hzu⟩
  rcases hzT with ⟨htl, htu⟩
  rcases hq with ⟨hql, hqu⟩
  constructor
  · constructor <;> linarith
  constructor <;> constructor <;> linarith

end OptimalG.Certificates.Compact
