import OptimalG.Finite

/-!
# The expectation-preserving slice correction

This is the finite weighted algebra of Section 5.1, Step 2, Eq. (5.5).
The predicate `low` represents the voters with rank below the threshold.
The stability consequences are explicit hypotheses: the centered score has
nonnegative expectation and the supported-candidate correction has expectation
zero. No existence of verifier coefficients is asserted here.
-/

namespace OptimalG

open scoped BigOperators

/-- The unnormalized expectation restricted to the low-rank voters. -/
noncomputable def lowExpectation {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (f : V → ℝ) : ℝ :=
  expectation w (fun v => if low v then f v else 0)

/-- The last, piecewise-defined term of Eq. (5.5). -/
noncomputable def sliceCorrection {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low]
    (φ c : V → ℝ) (v : V) : ℝ :=
  if low v then c v
  else φ v * (lowExpectation w low c / lowExpectation w low φ)

/-- Split a finite expectation into its low and complementary contributions. -/
theorem expectation_split {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (f : V → ℝ) :
    expectation w f = lowExpectation w low f +
      expectation w (fun v => if low v then 0 else f v) := by
  unfold lowExpectation expectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : low v <;> simp [h]

/-- Exact cancellation of the low-rank normalization in Eq. (5.5). -/
theorem expectation_sliceCorrection {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (φ c : V → ℝ)
    (hA : lowExpectation w low φ ≠ 0) :
    expectation w (sliceCorrection w low φ c) =
      (lowExpectation w low c / lowExpectation w low φ) * expectation w φ := by
  let A := lowExpectation w low φ
  let B := lowExpectation w low c
  have hpoint : sliceCorrection w low φ c = fun v =>
      (if low v then c v else 0) +
      (B / A) * (if low v then 0 else φ v) := by
    funext v
    by_cases h : low v <;> simp [sliceCorrection, A, B, h, mul_comm]
  rw [hpoint, expectation_add, expectation_smul]
  change B + (B / A) * expectation w (fun v => if low v then 0 else φ v) =
    (B / A) * expectation w φ
  rw [expectation_split w low φ]
  change B + (B / A) * expectation w (fun v => if low v then 0 else φ v) =
    (B / A) * (A + expectation w (fun v => if low v then 0 else φ v))
  have hA' : A ≠ 0 := hA
  field_simp

/-- Nonnegative low corrections yield a nonnegative normalization coefficient. -/
theorem correction_coefficient_nonneg {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (φ c : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hc : ∀ v, low v → 0 ≤ c v)
    (hA : 0 < lowExpectation w low φ) :
    0 ≤ lowExpectation w low c / lowExpectation w low φ := by
  apply div_nonneg _ (le_of_lt hA)
  apply Finset.sum_nonneg
  intro v _
  apply mul_nonneg (hw v)
  by_cases h : low v
  · simpa [h] using hc v h
  · simp [h]

/-- Stability of the reference candidate makes the expected correction positive. -/
theorem expectation_sliceCorrection_nonneg {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (φ c : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hc : ∀ v, low v → 0 ≤ c v)
    (hA : 0 < lowExpectation w low φ) (hφ : 0 ≤ expectation w φ) :
    0 ≤ expectation w (sliceCorrection w low φ c) := by
  rw [expectation_sliceCorrection w low φ c (ne_of_gt hA)]
  exact mul_nonneg (correction_coefficient_nonneg w low φ c hw hc hA) hφ

/-- Eq. (5.5) does not decrease the expected slice width. The coefficient β
may be arbitrary for this algebraic implication, since the k-term has mean zero. -/
theorem expected_slice_le_offset {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low]
    (φ c q k : V → ℝ) (β : ℝ)
    (hw : ∀ v, 0 ≤ w v) (hc : ∀ v, low v → 0 ≤ c v)
    (hA : 0 < lowExpectation w low φ) (hφ : 0 ≤ expectation w φ)
    (hk : expectation w k = 0) :
    expectation w q ≤ expectation w
      (fun v => q v + β * k v + sliceCorrection w low φ c v) := by
  rw [expectation_add, expectation_add, expectation_smul, hk]
  have hcmean := expectation_sliceCorrection_nonneg w low φ c hw hc hA hφ
  linarith

end OptimalG
