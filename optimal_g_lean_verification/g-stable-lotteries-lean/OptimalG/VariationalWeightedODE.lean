import OptimalG.VariationalTentFlow

/-!
# ODEs for continuous weighted controls

This module applies the same full-interval Picard construction to the weighted
fields used to approximate the essential-infimum trajectory.
-/

namespace OptimalG.Variational

open Set Metric
open scoped NNReal Topology

/-- A uniform state Lipschitz constant of 9.5 is small enough for a single
Picard ball on the entire interval of length .1. -/
theorem exists_continuation_interval_trajectory (F : ℝ → ℝ → ℝ) (x0 : ℝ)
    (hLip : ∀ z ∈ Icc zStart zEnd, LipschitzWith (19 / 2 : ℝ≥0) (F z))
    (hCont : ∀ u, ContinuousOn (fun z => F z u) (Icc zStart zEnd)) :
    ∃ Y : ℝ → ℝ, Y zStart = x0 ∧
      ∀ z ∈ Icc zStart zEnd, HasDerivWithinAt Y (F z (Y z)) (Icc zStart zEnd) z := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hCont x0)
  let B : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  let t0 : Icc zStart zEnd := ⟨zStart, by norm_num [zStart, zEnd]⟩
  have hpic : IsPicardLindelof F t0 x0 (2 * B) 0 (20 * B) (19 / 2) := by
    constructor
    · intro t ht
      exact (hLip t ht).lipschitzOnWith
    · intro x _
      exact hCont x
    · intro t ht x hx
      have hbase : ‖F t x0‖ ≤ (B : ℝ) := (hC t ht).trans (le_max_left _ _)
      have hlip := (hLip t ht).dist_le_mul x x0
      have hdist : dist x x0 ≤ 2 * (B : ℝ) := by
        simpa only [mem_closedBall, NNReal.coe_mul, NNReal.coe_ofNat] using hx
      have htri := norm_add_le (F t x - F t x0) (F t x0)
      rw [sub_add_cancel] at htri
      rw [dist_eq_norm] at hlip
      norm_num only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_mul] at hlip ⊢
      nlinarith
    · change (20 : ℝ) * B * max (zEnd - zStart) (zStart - zStart) ≤ 2 * B - 0
      norm_num [zStart, zEnd]
      ring_nf
      exact le_rfl
  exact hpic.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

def IsFieldTrajectory (F : ℝ → ℝ → ℝ) (x0 : ℝ) (Y : ℝ → ℝ) : Prop :=
  Y zStart = x0 ∧ ∀ z ∈ Icc zStart zEnd,
    HasDerivWithinAt Y (F z (Y z)) (Icc zStart zEnd) z

theorem IsFieldTrajectory.continuous {F : ℝ → ℝ → ℝ} {x0 : ℝ} {Y : ℝ → ℝ}
    (h : IsFieldTrajectory F x0 Y) : ContinuousOn Y (Icc zStart zEnd) :=
  fun z hz => (h.2 z hz).continuousWithinAt

theorem IsFieldTrajectory.right_derivative {F : ℝ → ℝ → ℝ} {x0 : ℝ} {Y : ℝ → ℝ}
    (h : IsFieldTrajectory F x0 Y) {z : ℝ} (hz : z ∈ Ico zStart zEnd) :
    HasDerivWithinAt Y (F z (Y z)) (Ici z) z :=
  (h.2 z ⟨hz.1, hz.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hz)

theorem Admissible.exists_frozenTentTrajectory
    {lam lamRef : ℝ} {d dRef : LowRankData} (h : Admissible lam d) (href : Admissible lamRef dRef)
    (Y : ℝ → ℝ) (hY : ContinuousOn Y (Icc zStart zEnd)) {eps : ℝ} (heps : 0 < eps) :
    ∃ Z : ℝ → ℝ, IsFieldTrajectory (frozenTentField lam d lamRef dRef Y eps)
      (quadratic lam zStart - d.S) Z :=
  exists_continuation_interval_trajectory _ _
    (fun z _ => h.frozenTentField_lipschitz href Y heps z)
    (h.frozenTentField_continuous_time href Y hY heps)

/-- Every trajectory of the frozen tent average dominates the actual maximal
continuation at the same target data. -/
theorem Admissible.frozenTentTrajectory_above
    {lam lamRef : ℝ} {d dRef : LowRankData} (h : Admissible lam d) (href : Admissible lamRef dRef)
    (Yref : ℝ → ℝ) {eps : ℝ} (heps : 0 < eps) {Y Z : ℝ → ℝ}
    (hY : IsContinuation lam d Y)
    (hZ : IsFieldTrajectory (frozenTentField lam d lamRef dRef Yref eps)
      (quadratic lam zStart - d.S) Z) :
    ∀ z ∈ Icc zStart zEnd, Y z ≤ Z z := by
  apply scalar_ode_comparison (frozenTentField lam d lamRef dRef Yref eps) (19 / 2)
    Y Z (fun z => vectorField lam d z (Y z))
    (fun z => frozenTentField lam d lamRef dRef Yref eps z (Z z)) zStart zEnd
    (fun z _ => h.frozenTentField_lipschitz href Yref heps z)
    (continuation_continuous hY) hZ.continuous
    (fun z hz => hY.right_derivative hz) (fun z hz => hZ.right_derivative hz)
    (fun z _ => h.vectorField_le_frozenTentField href Yref heps z (Y z))
    (fun _ _ => le_rfl)
  exact (hY.1.trans hZ.1.symm).le

/-- Explicit continuous averaged controls approximate the continuation within
the stated Gronwall error throughout the whole interval. -/
theorem Admissible.exists_tentApproximation {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {Y : ℝ → ℝ} (hY : IsContinuation lam d Y)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ Z : ℝ → ℝ, IsFieldTrajectory (frozenTentField lam d lam d Y eps)
      (quadratic lam zStart - d.S) Z ∧
      ∀ z ∈ Icc zStart zEnd, Y z ≤ Z z ∧
        Z z ≤ Y z + gronwallBound 0 ((19 : ℝ) / 2) eps (z - zStart) := by
  obtain ⟨Z, hZ⟩ := h.exists_frozenTentTrajectory h Y (continuation_continuous hY) heps
  refine ⟨Z, hZ, ?_⟩
  apply scalar_ode_approximation_gap (frozenTentField lam d lam d Y eps) (19 / 2)
    Y Z (fun z => vectorField lam d z (Y z)) zStart zEnd eps heps.le
    (fun z _ => h.frozenTentField_lipschitz h Y heps z)
    (continuation_continuous hY) hZ.continuous
    (fun z hz => hY.right_derivative hz) (fun z hz => hZ.right_derivative hz)
    (fun z _ => h.tentField_gap Y heps z)
  exact hY.1.trans hZ.1.symm

end OptimalG.Variational
