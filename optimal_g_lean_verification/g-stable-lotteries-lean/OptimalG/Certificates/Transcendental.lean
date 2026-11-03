import OptimalG.Certificates.Interval
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt

/-!
# Kernel-proved exponential and square-root enclosures

The Taylor remainder is Mathlib's proved bound, not a floating-point library
call. Square-root candidate endpoints are accepted only after their squared
rational inequalities have been checked. Both interfaces permit untrusted
certificate generators to propose bounds without enlarging the axiom boundary.
-/

namespace OptimalG.Certificates

open scoped BigOperators

namespace RatInterval

def expTaylor (q : ℚ) (n : ℕ) : ℚ :=
  ∑ m ∈ Finset.range n, q ^ m / (m.factorial : ℚ)

def expUpper (q : ℚ) (n : ℕ) : ℚ :=
  expTaylor q n + q ^ n * (n + 1) / (n.factorial * n)

def expEnclosure (a : RatInterval) (n : ℕ) : Option RatInterval :=
  if 0 < n ∧ 0 ≤ a.lo ∧ a.hi ≤ 1 then
    some ⟨expTaylor a.lo n, expUpper a.hi n⟩
  else none

theorem expTaylor_cast (q : ℚ) (n : ℕ) :
    (expTaylor q n : ℝ) = ∑ m ∈ Finset.range n, (q : ℝ) ^ m / (m.factorial : ℝ) := by
  simp [expTaylor]

theorem expUpper_cast (q : ℚ) (n : ℕ) :
    (expUpper q n : ℝ) =
      (∑ m ∈ Finset.range n, (q : ℝ) ^ m / (m.factorial : ℝ)) +
        (q : ℝ) ^ n * (n + 1) / (n.factorial * n) := by
  simp [expUpper, expTaylor_cast]

theorem expEnclosure_contains {a b : RatInterval} {x : ℝ} {n : ℕ}
    (hx : a.Contains x) (hb : a.expEnclosure n = some b) : b.Contains (Real.exp x) := by
  unfold expEnclosure at hb
  split_ifs at hb with hdom
  rcases hdom with ⟨hn, hlo, hhi⟩
  have hb' : b = ⟨expTaylor a.lo n, expUpper a.hi n⟩ := (Option.some.inj hb).symm
  subst b
  have hlo' : (0 : ℝ) ≤ a.lo := by exact_mod_cast hlo
  have hhi' : (a.hi : ℝ) ≤ 1 := by exact_mod_cast hhi
  have hhi0 : (0 : ℝ) ≤ a.hi := hlo'.trans (hx.1.trans hx.2)
  constructor
  · change (expTaylor a.lo n : ℝ) ≤ Real.exp x
    rw [expTaylor_cast]
    exact (Real.sum_le_exp_of_nonneg hlo' n).trans (Real.exp_le_exp.mpr hx.1)
  · change Real.exp x ≤ (expUpper a.hi n : ℝ)
    rw [expUpper_cast]
    exact (Real.exp_le_exp.mpr hx.2).trans (Real.exp_bound' hhi0 hhi' hn)

/-- Verify proposed square-root endpoints using exact rational arithmetic. -/
def sqrtCheck (a b : RatInterval) : Bool :=
  decide (0 ≤ b.lo ∧ b.lo ^ 2 ≤ a.lo ∧ a.hi ≤ b.hi ^ 2 ∧ 0 ≤ b.hi)

theorem sqrtCheck_contains {a b : RatInterval} {x : ℝ}
    (hx : a.Contains x) (hb : a.sqrtCheck b = true) : b.Contains (Real.sqrt x) := by
  have hc : 0 ≤ b.lo ∧ b.lo ^ 2 ≤ a.lo ∧ a.hi ≤ b.hi ^ 2 ∧ 0 ≤ b.hi := by
    simpa [sqrtCheck] using hb
  have hl : (b.lo : ℝ) ^ 2 ≤ a.lo := by exact_mod_cast hc.2.1
  have hu : (a.hi : ℝ) ≤ (b.hi : ℝ) ^ 2 := by exact_mod_cast hc.2.2.1
  have hub : (0 : ℝ) ≤ b.hi := by exact_mod_cast hc.2.2.2
  exact ⟨Real.le_sqrt_of_sq_le (hl.trans hx.1), (Real.sqrt_le_left hub).mpr (hx.2.trans hu)⟩

end RatInterval

/-- The actual exponential propagation loss used by Appendix B.1. -/
theorem propagation_loss_lt :
    (6.19 : ℝ) / 4.53 * (Real.exp 0.453 - 1) < 0.784 := by
  have hexp := Real.exp_bound' (x := (0.453 : ℝ)) (by norm_num) (by norm_num)
    (n := 11) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hexp
  nlinarith

end OptimalG.Certificates
