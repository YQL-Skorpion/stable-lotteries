import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-! Explicit cumulative-slack transformations used in Appendix B.1. These
functions, rather than abstract perturbation hypotheses, realize both phases. -/
namespace OptimalG
open Set
open scoped NNReal

/-- Remove all slack accumulated between a and b. -/
noncomputable def flattenSlack (S : ℝ → ℝ) (a b r : ℝ) : ℝ :=
  S (min r a) + max 0 (S r-S b)

/-- Remove a proportion t of the slack accumulated before a. -/
noncomputable def drainSlack (S : ℝ → ℝ) (a t r : ℝ) : ℝ :=
  (1-t)*S r + t*max 0 (S r-S a)

theorem flattenSlack_eq_before {S : ℝ → ℝ} (hS : Monotone S)
    {a b r : ℝ} (hab : a ≤ b) (hr : r ≤ a) : flattenSlack S a b r = S r := by
  have hh : S r-S b ≤ 0 := sub_nonpos.mpr (hS (hr.trans hab))
  simp [flattenSlack, min_eq_left hr, max_eq_left hh]

theorem flattenSlack_eq_middle {S : ℝ → ℝ} (hS : Monotone S)
    {a b r : ℝ} (hr : r ∈ Icc a b) : flattenSlack S a b r = S a := by
  have hh : S r-S b ≤ 0 := sub_nonpos.mpr (hS hr.2)
  simp [flattenSlack, min_eq_right hr.1, max_eq_left hh]

theorem flattenSlack_eq_after {S : ℝ → ℝ} (hS : Monotone S)
    {a b r : ℝ} (hab : a ≤ b) (hr : b ≤ r) :
    flattenSlack S a b r = S r-(S b-S a) := by
  have hh : 0 ≤ S r-S b := sub_nonneg.mpr (hS hr)
  simp only [flattenSlack, min_eq_right (hab.trans hr), max_eq_right hh]
  ring

theorem flattenSlack_monotone {S : ℝ → ℝ} (hS : Monotone S) (a b : ℝ) :
    Monotone (flattenSlack S a b) := by
  intro r s hrs
  apply add_le_add
  · exact hS (min_le_min_right a hrs)
  · exact max_le_max le_rfl (sub_le_sub_right (hS hrs) _)

theorem flattenSlack_bounds {S : ℝ → ℝ} (hS : Monotone S)
    {a b : ℝ} (hab : a ≤ b) (r : ℝ) :
    S r-(S b-S a) ≤ flattenSlack S a b r ∧ flattenSlack S a b r ≤ S r := by
  by_cases hra : r ≤ a
  · rw [flattenSlack_eq_before hS hab hra]
    constructor
    · linarith [hS hab]
    · rfl
  by_cases hrb : r ≤ b
  · rw [flattenSlack_eq_middle hS ⟨(lt_of_not_ge hra).le, hrb⟩]
    constructor
    · linarith [hS hrb]
    · exact hS (lt_of_not_ge hra).le
  · rw [flattenSlack_eq_after hS hab (lt_of_not_ge hrb).le]
    constructor
    · rfl
    · linarith [hS hab]

theorem flattenSlack_continuous {S : ℝ → ℝ} (hS : Continuous S) (a b : ℝ) :
    Continuous (flattenSlack S a b) := by
  exact (hS.comp (continuous_id.min continuous_const)).add
    (continuous_const.max (hS.sub continuous_const))

theorem drainSlack_eq_before {S : ℝ → ℝ} (hS : Monotone S)
    {a t r : ℝ} (hr : r ≤ a) : drainSlack S a t r = (1-t)*S r := by
  simp [drainSlack, max_eq_left (sub_nonpos.mpr (hS hr))]

theorem drainSlack_eq_after {S : ℝ → ℝ} (hS : Monotone S)
    {a t r : ℝ} (hr : a ≤ r) : drainSlack S a t r = S r-t*S a := by
  simp only [drainSlack, max_eq_right (sub_nonneg.mpr (hS hr))]
  ring

theorem drainSlack_monotone {S : ℝ → ℝ} (hS : Monotone S)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (a : ℝ) : Monotone (drainSlack S a t) := by
  intro r s hrs
  exact add_le_add (mul_le_mul_of_nonneg_left (hS hrs) (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left (max_le_max le_rfl (sub_le_sub_right (hS hrs) _)) ht.1)

theorem drainSlack_continuous {S : ℝ → ℝ} (hS : Continuous S) (a t : ℝ) :
    Continuous (drainSlack S a t) := by
  exact (continuous_const.mul hS).add
    (continuous_const.mul (continuous_const.max (hS.sub continuous_const)))

theorem drainSlack_bounds {S : ℝ → ℝ} (hS : Monotone S)
    {a t r : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hSa : 0 ≤ S a) (hSr : 0 ≤ S r) :
    S r-t*S a ≤ drainSlack S a t r ∧ drainSlack S a t r ≤ S r := by
  by_cases hr : r ≤ a
  · rw [drainSlack_eq_before hS hr]
    have hm := mul_le_mul_of_nonneg_left (hS hr) ht.1
    have hn := mul_nonneg ht.1 hSr
    constructor <;> nlinarith
  · rw [drainSlack_eq_after hS (lt_of_not_ge hr).le]
    have hn := mul_nonneg ht.1 hSa
    constructor
    · rfl
    · linarith

/-- Monotonicity of retained slack is exactly the integrated score ceiling. -/
theorem retainedSlack_primitive_increment {S Q : ℝ → ℝ} (hS : Monotone S)
    {r s : ℝ} (hrs : r ≤ s) :
    (Q s-S s)-(Q r-S r) ≤ Q s-Q r := by
  linarith [hS hrs]

/-- Phase 1 has the claimed exact changes at every low test rank and every
rank above the removed middle interval. -/
theorem first_phase_exact {S : ℝ → ℝ} (hS : Monotone S)
    {a x s t r : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hax : a ≤ x) (hxs : x ≤ s) :
    (r ∈ Icc a x → flattenSlack (drainSlack S a t) x s r = S r-t*S a) ∧
    (s ≤ r → flattenSlack (drainSlack S a t) x s r = S r-t*S a-(S s-S x)) := by
  have hd := drainSlack_monotone hS ht a
  constructor
  · intro hr
    rw [flattenSlack_eq_before hd hxs hr.2, drainSlack_eq_after hS hr.1]
  · intro hr
    rw [flattenSlack_eq_after hd hxs hr,
      drainSlack_eq_after hS (hax.trans (hxs.trans hr)),
      drainSlack_eq_after hS (hax.trans hxs), drainSlack_eq_after hS hax]
    ring

end OptimalG
