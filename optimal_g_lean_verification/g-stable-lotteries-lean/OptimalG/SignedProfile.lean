import OptimalG.RelabeledCyclicProfile
import OptimalG.Finite

/-!
# Signed ranking perturbations and strictly positive profile weights

Signed six-order perturbations are represented as genuine weights on the finite
set of rankings. Adding a sufficiently small multiple to the uniform profile
makes every ranking weight positive while preserving mass and stationarity.
-/

namespace OptimalG
open scoped BigOperators

noncomputable def cyclicCoefficient : Fin 6 → ℝ := ![1/3, 1/3, 1/3, -1/3, -1/3, -1/3]

noncomputable def signedRankingWeight {P : Type*} [DecidableEq P] (orders : Fin 6 → P) (p : P) : ℝ :=
  ∑ i, if orders i = p then cyclicCoefficient i else 0

theorem signedRankingWeight_average {P : Type*} [Fintype P] [DecidableEq P]
    (orders : Fin 6 → P) (f : P → ℝ) :
    expectation (signedRankingWeight orders) f = signedSix (fun i => f (orders i)) := by
  unfold expectation signedRankingWeight
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner (i : Fin 6) : (∑ p, (if orders i = p then cyclicCoefficient i else 0) * f p) =
      cyclicCoefficient i * f (orders i) := by
    simp only [ite_mul, zero_mul]
    simp
  simp_rw [hinner]
  simp [Fin.sum_univ_succ, cyclicCoefficient, signedSix]
  ring

theorem signedRankingWeight_total {P : Type*} [Fintype P] [DecidableEq P]
    (orders : Fin 6 → P) : ∑ p, signedRankingWeight orders p = 0 := by
  have h := signedRankingWeight_average orders (fun _ => (1 : ℝ))
  simpa [expectation, signedSix] using h

/-- A strictly positive probability vector obtained by perturbing every ranking
of the full uniform profile. The perturbation coefficient is explicit. -/
theorem exists_positive_uniform_perturbation {P : Type*} [Fintype P] [Nonempty P]
    (W : P → ℝ) (hW : ∑ p, W p = 0) :
    ∃ eps : ℝ, 0 < eps ∧
      (∀ p, 0 < 1 / (Fintype.card P : ℝ) + eps * W p) ∧
      (∑ p, (1 / (Fintype.card P : ℝ) + eps * W p)) = 1 := by
  let S := ∑ p, |W p|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hN : (0 : ℝ) < Fintype.card P := by exact_mod_cast Fintype.card_pos
  let eps := (1 / (Fintype.card P : ℝ)) / (S + 1)
  have heps : 0 < eps := div_pos (div_pos (by norm_num) hN) (by linarith)
  have heq : eps * (S + 1) = 1 / (Fintype.card P : ℝ) :=
    div_mul_cancel₀ _ (by linarith)
  refine ⟨eps, heps, ?_, ?_⟩
  · intro p
    have hle : |W p| ≤ S := Finset.single_le_sum (fun p _ => abs_nonneg (W p)) (Finset.mem_univ p)
    have hw := neg_abs_le (W p)
    nlinarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hW]
    simp [ne_of_gt hN]

/-- A signed perturbation with zero candidate scores preserves a stationary
uniform baseline after multiplication by any real coefficient. -/
theorem stationary_uniform_perturbation {P C : Type*} [Fintype P]
    (W : P → ℝ) (score : P → C → ℝ) (mean eps : ℝ)
    (hbase : ∀ a, expectation (fun _ : P => 1 / (Fintype.card P : ℝ)) (fun p => score p a) = mean)
    (hzero : ∀ a, expectation W (fun p => score p a) = 0) :
    ∀ a, expectation (fun p => 1 / (Fintype.card P : ℝ) + eps * W p)
      (fun p => score p a) = mean := by
  intro a
  unfold expectation at *
  simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, hbase, hzero,
    mul_zero, add_zero]

end OptimalG
