import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Exact weak duality with residual box penalties. The approximate optimizer
only proposes multipliers; this theorem verifies their mathematical implication. -/
namespace OptimalG
open Finset

/-- A signed residual times a variable is bounded below by its smaller box-end
value. No sign assumption on the residual is needed. -/
theorem residual_box_lower {e lo hi w : ℝ} (hlo : lo ≤ w) (hhi : w ≤ hi) :
    min (e * lo) (e * hi) ≤ e * w := by
  by_cases he : 0 ≤ e
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hlo he)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hhi (le_of_not_ge he))

/-- Every nonpositive dual vector yields a rigorous lower objective bound,
including arbitrary residuals paid for using the explicit variable box. -/
theorem linear_dual_box_lower {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℝ) (b pi : I → ℝ) (c e lo hi w : J → ℝ)
    (hpi : ∀ i, pi i ≤ 0)
    (hrows : ∀ i, ∑ j, A i j * w j ≤ b i)
    (hlo : ∀ j, lo j ≤ w j) (hhi : ∀ j, w j ≤ hi j)
    (hresidual : ∀ j, c j = e j + ∑ i, pi i * A i j) :
    (∑ i, pi i * b i) + (∑ j, min (e j * lo j) (e j * hi j)) ≤ ∑ j, c j * w j := by
  have hrow := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => mul_le_mul_of_nonpos_left (hrows i) (hpi i))
  have hbox := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => residual_box_lower (e := e j) (hlo j) (hhi j))
  have hid : (∑ i, pi i * ∑ j, A i j * w j) + ∑ j, e j * w j = ∑ j, c j * w j := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hresidual j, add_mul, Finset.sum_mul]
    have hh : (∑ i, pi i * (A i j * w j)) = ∑ i, pi i * A i j * w j := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hh]
    ring
  rw [← hid]
  exact add_le_add hrow hbox

end OptimalG
