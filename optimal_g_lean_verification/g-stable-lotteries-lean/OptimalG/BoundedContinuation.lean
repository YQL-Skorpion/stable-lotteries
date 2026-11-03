import OptimalG.VariationalODE
import Mathlib.Analysis.ODE.ExistUnique

/-! Existence between bounded sub- and supersolutions, with any finite state
Lipschitz constant. Truncation supplies a bounded Picard ball on the entire interval. -/
namespace OptimalG.Variational
open Set Metric
open scoped NNReal

noncomputable def clipUnit (u : ℝ) : ℝ := max (-1) (min 1 u)

theorem clipUnit_bounds (u : ℝ) : clipUnit u ∈ Icc (-1 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem clipUnit_eq {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) : clipUnit u = u := by
  simp [clipUnit, min_eq_right hu.2, max_eq_right hu.1]

theorem clipUnit_lipschitz : LipschitzWith 1 clipUnit :=
  (LipschitzWith.id.const_min 1).const_max (-1)

/-- A bounded state truncation admits a trajectory for any finite state
Lipschitz constant, on an arbitrarily long compact time interval. -/
theorem exists_clipped_continuation (F : ℝ → ℝ → ℝ) (K : ℝ≥0)
    (a b x0 : ℝ) (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, LipschitzWith K (F t))
    (htime : ∀ u, ContinuousOn (fun t => F t u) (Icc a b)) :
    ∃ Y : ℝ → ℝ, Y a = x0 ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt Y (F t (clipUnit (Y t))) (Icc a b) t := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (htime 0)
  let B : ℝ≥0 := ⟨max C 0 + K, add_nonneg (le_max_right _ _) K.coe_nonneg⟩
  let T : ℝ≥0 := ⟨b-a, sub_nonneg.mpr hab⟩
  let t0 : Icc a b := ⟨a, ⟨le_rfl, hab⟩⟩
  have hclip (t : ℝ) (ht : t ∈ Icc a b) :
      LipschitzWith K (fun u => F t (clipUnit u)) := by
    simpa only [Function.comp_def, mul_one] using (hF t ht).comp clipUnit_lipschitz
  have hpic : IsPicardLindelof (fun t u => F t (clipUnit u)) t0 x0 (T*B) 0 B K := by
    constructor
    · intro t ht
      exact (hclip t ht).lipschitzOnWith
    · intro u hu
      exact htime (clipUnit u)
    · intro t ht u hu
      have hbase : ‖F t 0‖ ≤ max C 0 := (hC t ht).trans (le_max_left _ _)
      have hd := (hF t ht).dist_le_mul (clipUnit u) 0
      have hclipabs : |clipUnit u| ≤ 1 := abs_le.mpr (clipUnit_bounds u)
      have hprod := mul_le_mul_of_nonneg_left hclipabs K.coe_nonneg
      have htri := norm_add_le (F t (clipUnit u)-F t 0) (F t 0)
      rw [sub_add_cancel] at htri
      rw [Real.dist_eq, Real.dist_eq, sub_zero] at hd
      change ‖F t (clipUnit u)‖ ≤ max C 0 + K
      simpa only [Real.norm_eq_abs] using htri.trans (by
        change |F t (clipUnit u)-F t 0| + |F t 0| ≤ max C 0 + K
        rw [Real.norm_eq_abs] at hbase
        linarith)
    · change (B : ℝ) * max (b-a) (a-a) ≤ (b-a)*B - 0
      rw [sub_self, max_eq_left (sub_nonneg.mpr hab), sub_zero]
      exact le_of_eq (mul_comm _ _)
  exact hpic.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- The solution of the truncated field is a solution of the original field
whenever bounded lower and upper trajectories trap it. -/
theorem exists_continuation_between (F : ℝ → ℝ → ℝ) (K : ℝ≥0)
    (low high lowD highD : ℝ → ℝ) (a b x0 : ℝ) (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, LipschitzWith K (F t))
    (htime : ∀ u, ContinuousOn (fun t => F t u) (Icc a b))
    (hlow : ContinuousOn low (Icc a b)) (hhigh : ContinuousOn high (Icc a b))
    (hlowD : ∀ t ∈ Ico a b, HasDerivWithinAt low (lowD t) (Ici t) t)
    (hhighD : ∀ t ∈ Ico a b, HasDerivWithinAt high (highD t) (Ici t) t)
    (hsub : ∀ t ∈ Ico a b, lowD t ≤ F t (low t))
    (hsuper : ∀ t ∈ Ico a b, F t (high t) ≤ highD t)
    (hlowBound : ∀ t ∈ Icc a b, low t ∈ Icc (-1 : ℝ) 1)
    (hhighBound : ∀ t ∈ Icc a b, high t ∈ Icc (-1 : ℝ) 1)
    (hinit : low a ≤ x0 ∧ x0 ≤ high a) :
    ∃ Y : ℝ → ℝ, Y a = x0 ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt Y (F t (Y t)) (Icc a b) t) ∧
      ∀ t ∈ Icc a b, low t ≤ Y t ∧ Y t ≤ high t := by
  obtain ⟨Y, hYa, hYd⟩ := exists_clipped_continuation F K a b x0 hab hF htime
  let G := fun t u => F t (clipUnit u)
  have hG (t : ℝ) (ht : t ∈ Ico a b) : LipschitzWith K (G t) := by
    simpa only [G, Function.comp_def, mul_one] using (hF t ⟨ht.1, ht.2.le⟩).comp clipUnit_lipschitz
  have hYc : ContinuousOn Y (Icc a b) := fun t ht => (hYd t ht).continuousWithinAt
  have hYr (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt Y (G t (Y t)) (Ici t) t :=
    (hYd t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  have hlo : ∀ t ∈ Icc a b, low t ≤ Y t := by
    refine scalar_ode_comparison G K low Y lowD (fun t => G t (Y t)) a b
      hG hlow hYc hlowD hYr ?_ (fun _ _ => le_rfl) ?_
    · intro t ht
      dsimp [G]
      rw [clipUnit_eq (hlowBound t ⟨ht.1, ht.2.le⟩)]
      exact hsub t ht
    · simpa [hYa] using hinit.1
  have hhi : ∀ t ∈ Icc a b, Y t ≤ high t := by
    refine scalar_ode_comparison G K Y high (fun t => G t (Y t)) highD a b
      hG hYc hhigh hYr hhighD (fun _ _ => le_rfl) ?_ ?_
    · intro t ht
      dsimp [G]
      rw [clipUnit_eq (hhighBound t ⟨ht.1, ht.2.le⟩)]
      exact hsuper t ht
    · simpa [hYa] using hinit.2
  refine ⟨Y, hYa, ?_, fun t ht => ⟨hlo t ht, hhi t ht⟩⟩
  intro t ht
  have hmem : Y t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(hlowBound t ht).1.trans (hlo t ht), (hhi t ht).trans (hhighBound t ht).2⟩
  simpa only [clipUnit_eq hmem] using hYd t ht

end OptimalG.Variational
