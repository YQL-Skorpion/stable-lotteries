import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-!
# Sound exact rational interval arithmetic

Endpoints are rationals, and every arithmetic operation is exact. Theorems in
this module establish enclosure of the corresponding real operation. This is
the trusted mathematical layer for generated numerical certificates: generators
may choose endpoints, but cannot bypass these enclosure proofs.
-/

namespace OptimalG.Certificates

structure RatInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

namespace RatInterval

def Contains (a : RatInterval) (x : ℝ) : Prop :=
  (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)

def point (q : ℚ) : RatInterval := ⟨q, q⟩
def neg (a : RatInterval) : RatInterval := ⟨-a.hi, -a.lo⟩
def add (a b : RatInterval) : RatInterval := ⟨a.lo + b.lo, a.hi + b.hi⟩
def sub (a b : RatInterval) : RatInterval := a.add b.neg

def mul (a b : RatInterval) : RatInterval :=
  ⟨min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)),
   max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))⟩

/-- Reject a divisor interval that meets zero. -/
def reciprocal (a : RatInterval) : Option RatInterval :=
  if 0 < a.lo ∨ a.hi < 0 then some ⟨a.hi⁻¹, a.lo⁻¹⟩ else none

theorem point_contains (q : ℚ) : (point q).Contains (q : ℝ) :=
  ⟨le_rfl, le_rfl⟩

theorem neg_contains {a : RatInterval} {x : ℝ} (hx : a.Contains x) :
    a.neg.Contains (-x) := by
  simpa [Contains, neg] using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

theorem add_contains {a b : RatInterval} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.add b).Contains (x + y) := by
  simpa [Contains, add] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem sub_contains {a b : RatInterval} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.sub b).Contains (x - y) := by
  simpa [sub, sub_eq_add_neg] using add_contains hx (neg_contains hy)

private theorem mul_le_max_endpoints {l u x y : ℝ} (hl : l ≤ x) (hu : x ≤ u) :
    x * y ≤ max (l * y) (u * y) := by
  by_cases hy : 0 ≤ y
  · exact (mul_le_mul_of_nonneg_right hu hy).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right hl (le_of_not_ge hy)).trans (le_max_left _ _)

private theorem min_endpoints_le_mul {l u x y : ℝ} (hl : l ≤ x) (hu : x ≤ u) :
    min (l * y) (u * y) ≤ x * y := by
  by_cases hy : 0 ≤ y
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hl hy)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hu (le_of_not_ge hy))

theorem mul_contains {a b : RatInterval} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.mul b).Contains (x * y) := by
  have hll := min_endpoints_le_mul (y := (a.lo : ℝ)) hy.1 hy.2
  have hlu := min_endpoints_le_mul (y := (a.hi : ℝ)) hy.1 hy.2
  have hul := mul_le_max_endpoints (y := (a.lo : ℝ)) hy.1 hy.2
  have huu := mul_le_max_endpoints (y := (a.hi : ℝ)) hy.1 hy.2
  simp only [mul_comm y, mul_comm (b.lo : ℝ), mul_comm (b.hi : ℝ)] at hll hlu hul huu
  constructor
  · simp only [mul, Rat.cast_min, Rat.cast_mul]
    exact (min_le_min hll hlu).trans (min_endpoints_le_mul hx.1 hx.2)
  · simp only [mul, Rat.cast_max, Rat.cast_mul]
    exact (mul_le_max_endpoints hx.1 hx.2).trans (max_le_max hul huu)

theorem reciprocal_contains {a b : RatInterval} {x : ℝ}
    (hx : a.Contains x) (h : a.reciprocal = some b) : b.Contains x⁻¹ := by
  unfold reciprocal at h
  split_ifs at h with hsign
  · have hb : b = ⟨a.hi⁻¹, a.lo⁻¹⟩ := (Option.some.inj h).symm
    subst b
    simp only [Contains, Rat.cast_inv]
    rcases hsign with hpos | hneg
    · have hlo : (0 : ℝ) < a.lo := by exact_mod_cast hpos
      have hxp : 0 < x := hlo.trans_le hx.1
      exact ⟨inv_anti₀ hxp hx.2, inv_anti₀ hlo hx.1⟩
    · have hhi : (a.hi : ℝ) < 0 := by exact_mod_cast hneg
      have hxn : x < 0 := hx.2.trans_lt hhi
      have hlo : (a.lo : ℝ) < 0 := hx.1.trans_lt hxn
      exact ⟨(inv_le_inv_of_neg hhi hxn).mpr hx.2,
        (inv_le_inv_of_neg hxn hlo).mpr hx.1⟩

end RatInterval
end OptimalG.Certificates
