import OptimalG.VariationalControl
import OptimalG.VariationalODE
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Existence and uniqueness of the actual continuation

The control envelope is globally Lipschitz in its state and continuous in time,
even before any regularity of the measurable low-rank score is known. A Picard
ball covering the whole interval proves that (4.3) is well-defined for every
member of the admissible set.
-/

namespace OptimalG.Variational

open Set Metric
open scoped NNReal

/-- Equation (4.3) has a solution on its entire prescribed interval for every
admissible measurable low-rank function. -/
theorem Admissible.exists_continuation {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) : ∃ Y : ℝ → ℝ, IsContinuation lam d Y := by
  let x0 := quadratic lam zStart - d.S
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.vectorField_continuous_time x0).continuousOn
  let B : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  let t0 : Icc zStart zEnd := ⟨zStart, by norm_num [zStart, zEnd]⟩
  have hpic : IsPicardLindelof (vectorField lam d) t0 x0
      (2 * B) 0 (20 * B) (19 / 2) := by
    constructor
    · intro t ht
      exact (h.vectorField_lipschitz t).lipschitzOnWith
    · intro x hx
      exact (h.vectorField_continuous_time x).continuousOn
    · intro t ht x hx
      have hbase : ‖vectorField lam d t x0‖ ≤ (B : ℝ) :=
        (hC t ht).trans (le_max_left _ _)
      have hlip := (h.vectorField_lipschitz t).dist_le_mul x x0
      have hdist : dist x x0 ≤ 2 * (B : ℝ) := by
        simpa only [mem_closedBall, NNReal.coe_mul, NNReal.coe_ofNat] using hx
      have htri := norm_add_le (vectorField lam d t x - vectorField lam d t x0)
        (vectorField lam d t x0)
      rw [sub_add_cancel] at htri
      rw [dist_eq_norm] at hlip
      norm_num only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_mul] at hlip ⊢
      nlinarith
    · change (20 : ℝ) * B * max (zEnd - zStart) (zStart - zStart) ≤ 2 * B - 0
      norm_num [zStart, zEnd]
      ring_nf
      exact le_rfl
  exact hpic.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- Restrict a continuation's one-sided derivative to the right-hand filter. -/
theorem IsContinuation.right_derivative {lam : ℝ} {d : LowRankData} {Y : ℝ → ℝ}
    (hY : IsContinuation lam d Y) {z : ℝ} (hz : z ∈ Ico zStart zEnd) :
    HasDerivWithinAt Y (vectorField lam d z (Y z)) (Ici z) z :=
  (hY.2 z ⟨hz.1, hz.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hz)

/-- The continuation is uniquely determined on the interval where it is used. -/
theorem Admissible.continuation_unique {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {Y Z : ℝ → ℝ}
    (hY : IsContinuation lam d Y) (hZ : IsContinuation lam d Z) :
    EqOn Y Z (Icc zStart zEnd) := by
  apply scalar_ode_unique (vectorField lam d) (19 / 2) Y Z zStart zEnd
    (fun z _ => h.vectorField_lipschitz z)
    (continuation_continuous hY) (continuation_continuous hZ)
    (fun z hz => hY.right_derivative hz) (fun z hz => hZ.right_derivative hz)
  exact hY.1.trans hZ.1.symm

/-- The clipping constraint gives the primitive upper bound throughout the
continuation interval, independently of any terminal test. -/
theorem Admissible.continuation_le_quadratic {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {Y : ℝ → ℝ} (hY : IsContinuation lam d Y) :
    ∀ z ∈ Icc zStart zEnd, Y z ≤ quadratic lam z - d.S := by
  let Q : ℝ → ℝ := fun z => quadratic lam z - d.S
  have hQd (z : ℝ) : HasDerivAt Q (lam - z) z := by
    have hi : HasDerivAt (fun z : ℝ => z) 1 z := hasDerivAt_id z
    have hh := ((hi.const_mul lam).sub ((hi.pow 2).div_const 2)).sub_const d.S
    have hs : lam * 1 - ((↑(2 : ℕ) : ℝ) * z ^ (2 - 1) * 1) / 2 = lam - z := by
      norm_num
    rw [hs] at hh
    exact hh
  apply scalar_ode_comparison (fun z _ => lam - z) 0 Y Q
    (fun z => vectorField lam d z (Y z)) (fun z => lam - z) zStart zEnd
  · intro z _
    exact LipschitzWith.const (lam - z)
  · exact continuation_continuous hY
  · exact (continuous_iff_continuousAt.mpr (fun z => (hQd z).continuousAt)).continuousOn
  · intro z hz
    exact hY.right_derivative hz
  · intro z _
    exact (hQd z).hasDerivWithinAt
  · intro z _
    exact vectorField_le_line lam d z (Y z)
  · intro z _
    exact le_rfl
  · exact hY.1.le

noncomputable def continuation (lam : ℝ) (d : LowRankData) : ℝ → ℝ := by
  classical
  exact if h : Admissible lam d then Classical.choose h.exists_continuation else fun _ => 0

theorem Admissible.isContinuation {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) : IsContinuation lam d (continuation lam d) := by
  rw [continuation, dif_pos h]
  exact Classical.choose_spec h.exists_continuation

/-- Feasibility may equivalently use the now-constructed canonical solution. -/
theorem feasible_iff_canonical (lam : ℝ) :
    Feasible lam ↔ ∃ d, Admissible lam d ∧ PassesTerminalTests lam d (continuation lam d) := by
  constructor
  · rintro ⟨d, hd, Y, hY, htest⟩
    refine ⟨d, hd, ?_⟩
    intro z hz q hq
    have hz' : z ∈ Icc zStart zEnd := by
      exact ⟨(by norm_num [zStart, zTest] : zStart ≤ zTest).trans hz.1, hz.2⟩
    rw [← hd.continuation_unique hY hd.isContinuation hz']
    exact htest z hz q hq
  · rintro ⟨d, hd, htest⟩
    exact ⟨d, hd, continuation lam d, hd.isContinuation, htest⟩

end OptimalG.Variational
