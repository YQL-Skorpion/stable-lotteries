import OptimalG.FineGridRealization

/-! # Common odd grids for simultaneous finite election approximations -/

namespace OptimalG
open Filter Set
open scoped Topology BigOperators

noncomputable def oddGridIndex (n : ℕ) (r : ℝ) : ℕ := ⌊((2 * n + 3 : ℕ) : ℝ) * r⌋₊
noncomputable def oddGrid (n : ℕ) (r : ℝ) : ℝ := (oddGridIndex n r : ℝ) / (2 * n + 3 : ℕ)

theorem oddGrid_tendsto (r : ℝ) (hr : 0 ≤ r) : Tendsto (fun n => oddGrid n r) atTop (𝓝 r) := by
  have ht : Tendsto (fun n : ℕ => 2 * n + 2) atTop atTop := by
    refine tendsto_atTop.2 (fun k => ?_)
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  exact (lowerGrid_tendsto r hr).comp ht

theorem oddGridIndex_mono (n : ℕ) : Monotone (oddGridIndex n) := by
  intro r s hrs
  exact Nat.floor_mono (mul_le_mul_of_nonneg_left hrs (Nat.cast_nonneg _))

theorem oddGridIndex_le (n : ℕ) (r : ℝ) (hr : r ≤ 1) : oddGridIndex n r ≤ 2 * n + 3 := by
  exact Nat.floor_le_of_le (mul_le_of_le_one_right (Nat.cast_nonneg _) hr)

theorem eventually_odd_grid_difference (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1))
    (r s : ℝ) (hr : r ∈ Icc 0 1) (hs : s ∈ Icc 0 1) (hne : g r ≠ g s) :
    ∀ᶠ n in atTop, ∃ j ≤ 2 * n,
      g (((j + 2 : ℕ) : ℝ) / (2 * n + 3 : ℕ)) ≠ g (((j + 1 : ℕ) : ℝ) / (2 * n + 3 : ℕ)) := by
  have ht : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    refine tendsto_atTop.2 (fun k => ?_)
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  exact (eventually_exists_interior_grid_difference g hg r s hr hs hne).filter_mono ht

theorem expectation_tendsto {T : Type*} [Fintype T]
    (w : T → ℝ) (f : ℕ → T → ℝ) (f0 : T → ℝ)
    (hf : ∀ t, Tendsto (fun n => f n t) atTop (𝓝 (f0 t))) :
    Tendsto (fun n => expectation w (f n)) atTop (𝓝 (expectation w f0)) := by
  have hc : Continuous (fun vals : T → ℝ => expectation w vals) := by unfold expectation; fun_prop
  exact hc.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hf)

theorem tendsto_vec3 (f g h : ℕ → ℝ) (a b c : ℝ)
    (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b)) (hh : Tendsto h atTop (𝓝 c)) :
    ∀ i : Fin 3, Tendsto (fun n => ![f n, g n, h n] i) atTop (𝓝 (![a, b, c] i)) := by
  intro i
  fin_cases i
  · exact hf
  · exact hg
  · exact hh

end OptimalG
