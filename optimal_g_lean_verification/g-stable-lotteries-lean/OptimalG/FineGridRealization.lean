import OptimalG.EqualVoterRealization
import OptimalG.ClippedElection
import OptimalG.InteriorGrid

/-! # Equal-voter realization under the original continuity hypothesis -/

namespace OptimalG
open Set Filter MeasureTheory
open scoped BigOperators Topology

theorem rankCut_const {m : ℕ} (u : ℝ) (k : ℕ) (hk : k ≤ m) :
    rankCut (fun _ : Fin m => u) k = (k : ℝ) * u := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkm : k < m := by omega
    rw [rankCut_succ (fun _ : Fin m => u) ⟨k, hkm⟩, ih (by omega)]
    push_cast
    ring

theorem cyclicStrength_uniform_grid {m : ℕ} (g : ℝ → ℝ) (a : Fin m) :
    cyclicStrength g a (1 / (m : ℝ)) =
      (g (((a.val + 2 : ℕ) : ℝ) / m) - g (((a.val + 1 : ℕ) : ℝ) / m)) /
        (3 * (1 / (m : ℝ))) := by
  unfold cyclicStrength
  rw [rankCut_const _ _ a.isLt.le]
  congr 2 <;> congr 1 <;> push_cast <;> ring

/-- Every sufficiently large odd support has the actual nonzero cyclic
perturbation needed for the exact score correction. -/
theorem eventually_odd_cyclicStrength (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 1)) (r s : ℝ)
    (hr : r ∈ Icc 0 1) (hs : s ∈ Icc 0 1) (hne : g r ≠ g s) :
    ∀ᶠ n in atTop, ∃ a b c : Fin (2 * n + 3),
      a.val + 1 = b.val ∧ b.val + 1 = c.val ∧
        cyclicStrength (clippedActivation g) a (1 / (2 * n + 3 : ℕ)) ≠ 0 := by
  have ht : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    refine tendsto_atTop.2 (fun k => ?_)
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  have he := (eventually_exists_interior_grid_difference (clippedActivation g)
    (clippedActivation_continuous g hg).continuousOn r s hr hs
    (by simpa only [clippedActivation_eq g r hr, clippedActivation_eq g s hs] using hne)).filter_mono ht
  filter_upwards [he] with n hn
  obtain ⟨k, hk, hdiff⟩ := hn
  change k ≤ 2 * n at hk
  let a : Fin (2 * n + 3) := ⟨k, by omega⟩
  let b : Fin (2 * n + 3) := ⟨k + 1, by omega⟩
  let c : Fin (2 * n + 3) := ⟨k + 2, by omega⟩
  refine ⟨a, b, c, rfl, by rfl, ?_⟩
  rw [cyclicStrength_uniform_grid]
  exact div_ne_zero (sub_ne_zero.mpr hdiff) (mul_ne_zero (by norm_num)
    (one_div_ne_zero (by positivity)))

/-- The full-support realization theorem uses only continuity on the rank
interval, actual rank-interval activations, and the finite grid condition. -/
theorem full_support_equal_voter_realization_on {V : Type*} [Fintype V] {n m : ℕ} [NeZero m]
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1))
    (e : PairedSupport n ≃ Fin m) (a b c : Fin m)
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (hstrength : cyclicStrength (clippedActivation g) a (1 / (m : ℝ)) ≠ 0)
    (orders : V → Equiv.Perm (Fin m)) (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hwsum : ∑ v, w v = 1)
    (hstationary : ∀ x, expectation w (fun v => orderedActivation g (uniformVector m) (orders v) x) =
      ∫ r in (0 : ℝ)..1, g r)
    (rho : Fin m → ℝ) (hrho : ∀ x, 0 ≤ rho x) (reference : Fin m) (href : rho reference = 0)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hexcess : lam * expectation w (fun v => maximumGap (fun x => ((orders v).symm x).val) rho) <
      expectation w (fun v => expectation (uniformVector m)
        (runningMin (fun x => ((orders v).symm x).val) rho))) :
    WitnessAbove g (1 + 2 * lam) := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hnonneg : ∀ x : Fin m, 0 ≤ uniformVector m x := fun x => by
    exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  have htotal : ∑ x : Fin m, uniformVector m x = 1 := by simp [uniformVector, hm]
  apply (witnessAbove_clipped_iff g _).mp
  apply full_support_equal_voter_realization (clippedActivation g) (clippedActivation_continuous g hg)
    e a b c hab hbc hstrength orders w hw hwsum _ rho hrho reference href lam hlam hexcess
  intro x
  simp_rw [clipped_scoreExtension_eq_orderedActivation g hg _ _ (uniformVector m)
    hnonneg htotal (one_div_ne_zero hm), clippedActivation_mean]
  exact hstationary x

end OptimalG
