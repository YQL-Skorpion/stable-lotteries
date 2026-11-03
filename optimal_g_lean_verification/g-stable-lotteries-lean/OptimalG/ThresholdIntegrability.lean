import OptimalG.ThresholdGeometry

/-! Any function of the finite threshold set is integrable on bounded intervals.
No measurability assumption on mass-indexed verifier coefficients is needed. -/
namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

theorem intervalIntegrable_indicator_const (s : Set ℝ) (hs : MeasurableSet s)
    (c a b : ℝ) : IntervalIntegrable (s.indicator (fun _ => c)) volume a b := by
  exact intervalIntegrable_iff.mpr
    ((intervalIntegrable_iff.mp (intervalIntegrable_const (c := c))).indicator hs)

theorem thresholdSet_fiber_measurable {n : ℕ} (rho : Fin n → ℝ)
    (S : Finset (Fin n)) : MeasurableSet {t : ℝ | thresholdSet rho t = S} := by
  classical
  have heq : {t : ℝ | thresholdSet rho t = S} =
      ⋂ i : Fin n, {t : ℝ | (t < rho i ↔ i ∈ S)} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h i
      have hh := congrArg (fun T : Finset (Fin n) => i ∈ T) h
      simpa [thresholdSet] using hh
    · intro h
      ext i
      simpa [thresholdSet] using h i
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ∈ S
  · simpa only [hi, iff_true, Set.Iio_def] using (measurableSet_Iio (a := rho i))
  · simpa only [hi, iff_false, not_lt, Set.Ici_def] using (measurableSet_Ici (a := rho i))

theorem thresholdSet_function_integrable {n : ℕ} (rho : Fin n → ℝ)
    (H : Finset (Fin n) → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun t => H (thresholdSet rho t)) volume a b := by
  classical
  let f : Finset (Fin n) → ℝ → ℝ := fun S =>
    {t : ℝ | thresholdSet rho t = S}.indicator (fun _ => H S)
  have heq : (fun t => H (thresholdSet rho t)) = ∑ S : Finset (Fin n), f S := by
    funext t
    simp only [Finset.sum_apply, f, Set.indicator, Set.mem_setOf_eq]
    simp
  rw [heq]
  exact IntervalIntegrable.sum Finset.univ (fun S _ =>
    intervalIntegrable_indicator_const _ (thresholdSet_fiber_measurable rho S) (H S) a b)

/-- Extension by a constant on negative thresholds preserves local integrability. -/
theorem extendedThreshold_integrable {n : ℕ} (rho : Fin n → ℝ)
    (H : Finset (Fin n) → ℝ) (lam a b : ℝ) :
    IntervalIntegrable (fun t => if t < 0 then lam else H (thresholdSet rho t)) volume a b := by
  classical
  have hleft := intervalIntegrable_indicator_const (Iio (0 : ℝ)) measurableSet_Iio lam a b
  have hright := intervalIntegrable_iff.mpr
    ((intervalIntegrable_iff.mp (thresholdSet_function_integrable rho H a b)).indicator
      (measurableSet_Ici (a := (0 : ℝ))))
  convert hleft.add hright using 1
  funext t
  by_cases ht : t < 0
  · simp [Set.indicator, Set.mem_Iio, Set.mem_Ici, ht, not_le.mpr ht]
  · simp [Set.indicator, Set.mem_Iio, Set.mem_Ici, ht, le_of_not_gt ht]

end OptimalG
