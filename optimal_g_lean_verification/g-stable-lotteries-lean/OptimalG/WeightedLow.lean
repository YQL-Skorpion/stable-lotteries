import OptimalG.Offsets

/-! Finite averaging with weights proportional to positive low-rank scores. -/
namespace OptimalG
open scoped BigOperators

noncomputable def weightedLow {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (score f : V → ℝ) : ℝ :=
  lowExpectation w low (fun v => score v * f v) / lowExpectation w low score

theorem lowExpectation_add {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (f g : V → ℝ) :
    lowExpectation w low (fun v => f v + g v) = lowExpectation w low f + lowExpectation w low g := by
  unfold lowExpectation expectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : low v <;> simp [h, mul_add]

theorem lowExpectation_sub {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (f g : V → ℝ) :
    lowExpectation w low (fun v => f v - g v) = lowExpectation w low f - lowExpectation w low g := by
  unfold lowExpectation expectation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : low v <;> simp [h, mul_sub]

theorem lowExpectation_smul {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (f : V → ℝ) (c : ℝ) :
    lowExpectation w low (fun v => c * f v) = c * lowExpectation w low f := by
  unfold lowExpectation expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : low v <;> simp [h] <;> ring

theorem weightedLow_congr {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (score f g : V → ℝ)
    (hfg : ∀ v, low v → f v = g v) : weightedLow w low score f = weightedLow w low score g := by
  unfold weightedLow lowExpectation expectation
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : low v
  · simp [h, hfg v h]
  · simp [h]

theorem weightedLow_const {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (score : V → ℝ) (c : ℝ)
    (hA : lowExpectation w low score ≠ 0) : weightedLow w low score (fun _ => c) = c := by
  simp only [weightedLow, mul_comm _ c, lowExpectation_smul]
  exact mul_div_cancel_right₀ c hA

theorem weightedLow_add {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (score f g : V → ℝ) :
    weightedLow w low score (fun v => f v + g v) = weightedLow w low score f + weightedLow w low score g := by
  simp only [weightedLow, mul_add, lowExpectation_add, add_div]

theorem weightedLow_sub {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (score f g : V → ℝ) :
    weightedLow w low score (fun v => f v - g v) = weightedLow w low score f - weightedLow w low score g := by
  simp only [weightedLow, mul_sub, lowExpectation_sub, sub_div]

theorem weightedLow_smul {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (score f : V → ℝ) (c : ℝ) :
    weightedLow w low score (fun v => c * f v) = c * weightedLow w low score f := by
  simp only [weightedLow, mul_left_comm _ c, lowExpectation_smul, mul_div_assoc]

theorem weightedLow_mono {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (score f g : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hs : ∀ v, low v → 0 ≤ score v)
    (hA : 0 < lowExpectation w low score) (hfg : ∀ v, low v → f v ≤ g v) :
    weightedLow w low score f ≤ weightedLow w low score g := by
  apply div_le_div_of_nonneg_right _ hA.le
  apply expectation_mono hw
  intro v
  by_cases h : low v
  · simp only [if_pos h]
    exact mul_le_mul_of_nonneg_left (hfg v h) (hs v h)
  · simp [h]

theorem weightedLow_div_score {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (score f : V → ℝ)
    (hs : ∀ v, low v → score v ≠ 0) :
    weightedLow w low score (fun v => f v / score v) =
      lowExpectation w low f / lowExpectation w low score := by
  unfold weightedLow lowExpectation expectation
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : low v
  · simp only [if_pos h]
    rw [mul_div_cancel₀ _ (hs v h)]
  · simp [h]

end OptimalG
