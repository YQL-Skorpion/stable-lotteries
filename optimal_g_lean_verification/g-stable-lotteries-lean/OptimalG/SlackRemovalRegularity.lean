import OptimalG.SlackRemoval
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction

/-! Regularity and exact algebra of the concrete slack-removal phases. -/
namespace OptimalG
open Set
open scoped NNReal

theorem flattenSlack_lipschitz {S : ℝ → ℝ} {K : ℝ≥0}
    (hS : LipschitzWith K S) (a b : ℝ) :
    LipschitzWith (K+K) (flattenSlack S a b) := by
  have hleft : LipschitzWith K (fun r => S (min r a)) := by
    simpa only [Function.comp_def, mul_one, id_eq] using hS.comp (LipschitzWith.id.min_const a)
  have hright : LipschitzWith K (fun r => max 0 (S r-S b)) := by
    have hh : LipschitzWith K (fun r => S r-S b) := by
      simpa only [add_zero] using hS.sub (LipschitzWith.const (S b))
    exact hh.const_max 0
  exact hleft.add hright

theorem drainSlack_lipschitz {S : ℝ → ℝ} {K : ℝ≥0}
    (hS : LipschitzWith K S) (a t : ℝ) :
    LipschitzWith (‖1-t‖₊*K+‖t‖₊*K) (drainSlack S a t) := by
  have hleft : LipschitzWith (‖1-t‖₊*K) (fun r => (1-t)*S r) := by
    simpa only [Function.comp_def, smul_eq_mul] using (lipschitzWith_smul (1-t)).comp hS
  have hbase : LipschitzWith K (fun r => S r-S a) := by
    simpa only [add_zero] using hS.sub (LipschitzWith.const (S a))
  have hright : LipschitzWith (‖t‖₊*K) (fun r => t*max 0 (S r-S a)) := by
    simpa only [Function.comp_def, smul_eq_mul] using (lipschitzWith_smul t).comp (hbase.const_max 0)
  exact hleft.add hright

/-- Removing two adjacent intervals is exactly removal of their union. -/
theorem flattenSlack_adjacent {S : ℝ → ℝ} (hS : Monotone S)
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    flattenSlack (flattenSlack S a b) b c = flattenSlack S a c := by
  funext r
  have hF := flattenSlack_monotone hS a b
  by_cases hrb : r ≤ b
  · rw [flattenSlack_eq_before hF hbc hrb]
    by_cases hra : r ≤ a
    · rw [flattenSlack_eq_before hS hab hra, flattenSlack_eq_before hS (hab.trans hbc) hra]
    · rw [flattenSlack_eq_middle hS ⟨(lt_of_not_ge hra).le,hrb⟩,
        flattenSlack_eq_middle hS ⟨(lt_of_not_ge hra).le,hrb.trans hbc⟩]
  · by_cases hrc : r ≤ c
    · rw [flattenSlack_eq_middle hF ⟨(lt_of_not_ge hrb).le,hrc⟩,
        flattenSlack_eq_middle hS ⟨hab,le_rfl⟩,
        flattenSlack_eq_middle hS ⟨hab.trans (lt_of_not_ge hrb).le,hrc⟩]
    · rw [flattenSlack_eq_after hF hbc (lt_of_not_ge hrc).le,
        flattenSlack_eq_after hS hab (lt_of_not_ge hrb).le,
        flattenSlack_eq_after hS hab hbc,
        flattenSlack_eq_middle hS ⟨hab,le_rfl⟩,
        flattenSlack_eq_after hS (hab.trans hbc) (lt_of_not_ge hrc).le]
      ring

/-- The actual final cumulative slack is constant throughout the whole middle
interval, and has the exact decrease asserted by the two-phase bookkeeping. -/
theorem two_phase_middle {S : ℝ → ℝ} (hS : Monotone S)
    {a x s z t r : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hax : a ≤ x) (hxs : x ≤ s) (hsz : s ≤ z) (hr : r ∈ Icc x z) :
    flattenSlack (flattenSlack (drainSlack S a t) x s) s z r = S x-t*S a := by
  rw [flattenSlack_adjacent (drainSlack_monotone hS ht a) hxs hsz,
    flattenSlack_eq_middle (drainSlack_monotone hS ht a) hr,
    drainSlack_eq_after hS hax]

/-- At and above the final endpoint, the two-phase change is the prefix drain
plus precisely the slack from the two middle intervals. -/
theorem two_phase_after {S : ℝ → ℝ} (hS : Monotone S)
    {a x s z t r : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hax : a ≤ x) (hxs : x ≤ s) (hsz : s ≤ z) (hr : z ≤ r) :
    flattenSlack (flattenSlack (drainSlack S a t) x s) s z r =
      S r-t*S a-(S s-S x)-(S z-S s) := by
  rw [flattenSlack_adjacent (drainSlack_monotone hS ht a) hxs hsz]
  rw [(first_phase_exact hS ht hax (hxs.trans hsz)).2 hr]
  ring

end OptimalG
