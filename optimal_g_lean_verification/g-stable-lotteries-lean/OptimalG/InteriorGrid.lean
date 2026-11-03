import OptimalG.ElectionOneLimit

/-!
# A nonzero interior grid difference for every sufficiently fine support

Continuous nonconstant activations must differ at adjacent interior grid points
for every sufficiently large denominator. This supplies the nonzero cyclic
strength in the equal-voter construction, including arbitrarily large odd sizes.
-/

namespace OptimalG
open Set Filter
open scoped Topology

noncomputable def interiorGridNumerator (n : ℕ) (r : ℝ) : ℕ :=
  ⌊((n + 1 : ℕ) : ℝ) * r⌋₊ + 1

noncomputable def interiorGrid (n : ℕ) (r : ℝ) : ℝ :=
  (interiorGridNumerator n r : ℝ) / (n + 3 : ℕ)

theorem interiorGridNumerator_bounds (n : ℕ) (r : ℝ) (hr : r ∈ Icc 0 1) :
    1 ≤ interiorGridNumerator n r ∧ interiorGridNumerator n r ≤ n + 2 := by
  have hfloor : ⌊((n + 1 : ℕ) : ℝ) * r⌋₊ ≤ n + 1 :=
    Nat.floor_le_of_le (mul_le_of_le_one_right (Nat.cast_nonneg _) hr.2)
  unfold interiorGridNumerator
  omega

theorem interiorGrid_mem_Ioo (n : ℕ) (r : ℝ) (hr : r ∈ Icc 0 1) :
    interiorGrid n r ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨hlo, hhi⟩ := interiorGridNumerator_bounds n r hr
  have hden : (0 : ℝ) < (n + 3 : ℕ) := by positivity
  constructor
  · apply div_pos _ hden
    exact_mod_cast (show 0 < interiorGridNumerator n r by omega)
  · apply (div_lt_one hden).mpr
    exact_mod_cast (show interiorGridNumerator n r < n + 3 by omega)

theorem interiorGrid_error (n : ℕ) (r : ℝ) (hr : r ∈ Icc 0 1) :
    r - 2 / ((n + 3 : ℕ) : ℝ) ≤ interiorGrid n r ∧
      interiorGrid n r ≤ r + 1 / ((n + 3 : ℕ) : ℝ) := by
  have hden : (0 : ℝ) < (n + 3 : ℕ) := by positivity
  have hfloorLo := Nat.lt_floor_add_one (((n + 1 : ℕ) : ℝ) * r)
  have hfloorHi := Nat.floor_le (mul_nonneg (Nat.cast_nonneg (n + 1)) hr.1)
  have htwo : (2 : ℝ) / (n + 3 : ℕ) * (n + 3 : ℕ) = 2 := div_mul_cancel₀ _ (ne_of_gt hden)
  have hone : (1 : ℝ) / (n + 3 : ℕ) * (n + 3 : ℕ) = 1 := div_mul_cancel₀ _ (ne_of_gt hden)
  unfold interiorGrid interiorGridNumerator
  constructor
  · apply (le_div_iff₀ hden).mpr
    push_cast
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hfloorLo htwo
    nlinarith [hr.2]
  · apply (div_le_iff₀ hden).mpr
    push_cast
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hfloorHi hone
    nlinarith [hr.1]

theorem interiorGrid_tendsto (r : ℝ) (hr : r ∈ Icc 0 1) :
    Tendsto (fun n => interiorGrid n r) atTop (𝓝 r) := by
  have hi : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 3 : ℕ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 3)
  have htwo : Tendsto (fun n : ℕ => (2 : ℝ) / (n + 3 : ℕ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp (tendsto_add_atTop_nat 3)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using (tendsto_const_nhds (x := r)).sub htwo)
    (by simpa using (tendsto_const_nhds (x := r)).add hi)
  · intro n
    simpa only [Nat.cast_add, Nat.cast_ofNat] using (interiorGrid_error n r hr).1
  · intro n
    simpa only [Nat.cast_add, Nat.cast_ofNat, one_div] using (interiorGrid_error n r hr).2

/-- Unequal interior grid values force a consecutive unequal pair. -/
theorem exists_adjacent_grid_ne (g : ℝ → ℝ) (n j k : ℕ)
    (hj : 1 ≤ j) (hjn : j ≤ n + 2) (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    (hne : g ((j : ℝ) / (n + 3 : ℕ)) ≠ g ((k : ℝ) / (n + 3 : ℕ))) :
    ∃ r ≤ n, g (((r + 2 : ℕ) : ℝ) / (n + 3 : ℕ)) ≠
      g (((r + 1 : ℕ) : ℝ) / (n + 3 : ℕ)) := by
  by_contra! hnone
  have hconst : ∀ q : ℕ, 1 ≤ q → q ≤ n + 2 →
      g ((q : ℝ) / (n + 3 : ℕ)) = g (1 / (n + 3 : ℕ)) := by
    intro q
    induction q with
    | zero => omega
    | succ q ih =>
      intro hq hqn
      by_cases hq0 : q = 0
      · subst q; simp
      · have hqpos : 1 ≤ q := by omega
        have hs := hnone (q - 1) (by omega)
        have h1 : q - 1 + 1 = q := by omega
        have h2 : q - 1 + 2 = q + 1 := by omega
        rw [h1, h2] at hs
        exact hs.trans (ih hqpos (by omega))
  exact hne ((hconst j hj hjn).trans (hconst k hk hkn).symm)

/-- Nonconstancy is detected inside every sufficiently fine grid, away from both
endpoints. No differentiability or monotonicity of the activation is needed. -/
theorem eventually_exists_interior_grid_difference (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 1)) (r s : ℝ)
    (hr : r ∈ Icc 0 1) (hs : s ∈ Icc 0 1) (hne : g r ≠ g s) :
    ∀ᶠ n in atTop, ∃ k ≤ n,
      g (((k + 2 : ℕ) : ℝ) / (n + 3 : ℕ)) ≠ g (((k + 1 : ℕ) : ℝ) / (n + 3 : ℕ)) := by
  have hlim (x : ℝ) (hx : x ∈ Icc 0 1) :
      Tendsto (fun n => g (interiorGrid n x)) atTop (𝓝 (g x)) := by
    apply (hg x hx).tendsto.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨interiorGrid_tendsto x hx,
      Eventually.of_forall (fun n => ⟨(interiorGrid_mem_Ioo n x hx).1.le,
        (interiorGrid_mem_Ioo n x hx).2.le⟩)⟩
  have hdiff : Tendsto (fun n => g (interiorGrid n r) - g (interiorGrid n s)) atTop (𝓝 (g r - g s)) :=
    (hlim r hr).sub (hlim s hs)
  filter_upwards [hdiff.eventually_ne (sub_ne_zero.mpr hne)] with n hn
  obtain ⟨hj, hjn⟩ := interiorGridNumerator_bounds n r hr
  obtain ⟨hk, hkn⟩ := interiorGridNumerator_bounds n s hs
  exact exists_adjacent_grid_ne g n (interiorGridNumerator n r) (interiorGridNumerator n s)
    hj hjn hk hkn (sub_ne_zero.mp hn)

end OptimalG
