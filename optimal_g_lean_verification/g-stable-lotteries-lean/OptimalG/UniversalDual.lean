import OptimalG.LinearDuality
import Mathlib.Data.Rat.Cast.Order

/-! Kernel-checkable rational dual certificates for the universal LP. -/
namespace OptimalG
open Finset

/-- All numerical assertions in a dual certificate are finite rational tests. -/
def checkRationalDual {n k : ℕ}
    (A : Fin k → Fin n → ℚ) (b pi : Fin k → ℚ) (c e lo hi : Fin n → ℚ) (bound : ℚ) : Bool :=
  decide ((∀ i, pi i ≤ 0) ∧ (∀ j, c j = e j + ∑ i, pi i * A i j) ∧
    bound ≤ (∑ i, pi i * b i) + ∑ j, min (e j * lo j) (e j * hi j))

/-- Soundness of the rational checker against arbitrary real-valued feasible
variables. The numerical certificate does not assume rationality of the primitive. -/
theorem checkRationalDual_sound {n k : ℕ}
    (A : Fin k → Fin n → ℚ) (b pi : Fin k → ℚ) (c e lo hi : Fin n → ℚ) (bound : ℚ)
    (hc : checkRationalDual A b pi c e lo hi bound = true)
    (w : Fin n → ℝ)
    (hrows : ∀ i, ∑ j, (A i j : ℝ) * w j ≤ b i)
    (hlo : ∀ j, (lo j : ℝ) ≤ w j) (hhi : ∀ j, w j ≤ hi j) :
    (bound : ℝ) ≤ ∑ j, (c j : ℝ) * w j := by
  have hh : (∀ i, pi i ≤ 0) ∧ (∀ j, c j = e j + ∑ i, pi i * A i j) ∧
      bound ≤ (∑ i, pi i * b i) + ∑ j, min (e j * lo j) (e j * hi j) := of_decide_eq_true hc
  have hdual := linear_dual_box_lower (fun i j => (A i j : ℝ))
    (fun i => (b i : ℝ)) (fun i => (pi i : ℝ)) (fun j => (c j : ℝ))
    (fun j => (e j : ℝ)) (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)) w
    (fun i => by exact_mod_cast hh.1 i) hrows hlo hhi
    (fun j => by exact_mod_cast hh.2.1 j)
  have hbound : (bound : ℝ) ≤ (∑ i, (pi i : ℝ) * b i) +
      ∑ j, min ((e j : ℝ) * lo j) ((e j : ℝ) * hi j) := by exact_mod_cast hh.2.2
  exact hbound.trans hdual

end OptimalG
