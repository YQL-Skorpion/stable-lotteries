import OptimalG.TwoClassProfile

/-! # Every strict finite-grid two-class violation is an actual distortion witness -/

namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

theorem two_class_grid_strict_witness (g : ℝ → ℝ) (hg : Continuous g)
    (lam : ℝ) (hlam : 0 ≤ lam) (h z k n : ℕ)
    (hh : 0 < h) (hz : 0 < z) (hk : k < h) [NeZero (h + z)]
    (e : PairedSupport n ≃ Fin (h + z)) (a b c : Fin (h + z))
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (hstrength : cyclicStrength g a (1 / (h + z : ℕ)) ≠ 0)
    (hR : 0 < centeredPrimitive g ((h : ℝ) / (h + z : ℕ)))
    (hdelta : 0 < centeredPrimitive g (((k + z : ℕ) : ℝ) / (h + z : ℕ)) -
      centeredPrimitive g ((k : ℝ) / (h + z : ℕ)))
    (hexcess : (lam - (k : ℝ) / (h + z : ℕ)) * centeredPrimitive g ((h : ℝ) / (h + z : ℕ)) <
      ((h : ℝ) / (h + z : ℕ)) *
        (centeredPrimitive g (((k + z : ℕ) : ℝ) / (h + z : ℕ)) -
          centeredPrimitive g ((k : ℝ) / (h + z : ℕ)))) :
    WitnessAbove g (1 + 2 * lam) := by
  let R := centeredPrimitive g ((h : ℝ) / (h + z : ℕ))
  let delta := centeredPrimitive g (((k + z : ℕ) : ℝ) / (h + z : ℕ)) -
    centeredPrimitive g ((k : ℝ) / (h + z : ℕ))
  let theta := R / (R + delta)
  have hden : 0 < R + delta := add_pos hR hdelta
  have hden0 : R + delta ≠ 0 := ne_of_gt hden
  have ht : theta ∈ Icc 0 1 := ⟨(div_pos hR hden).le, (div_le_one hden).mpr (le_add_of_nonneg_right hdelta.le)⟩
  have hbalance : theta * delta - (1 - theta) * R = 0 := by
    dsimp [theta]
    field_simp
    ring
  obtain ⟨orders, hs, hcost, hgap⟩ := exists_two_class_profile g hg h z k hh hz hk theta ht hbalance
  have hm : ((h + z : ℕ) : ℝ) ≠ 0 := by positivity
  have hscore : ∀ x, expectation (twoTypeWeight theta) (fun v =>
      scoreExtension g (orders v) x (uniformVector (h + z))) = ∫ r in (0 : ℝ)..1, g r := by
    intro x
    simp_rw [scoreExtension_eq_orderedActivation g hg _ _ (uniformVector (h + z)) (one_div_ne_zero hm)]
    exact hs x
  apply full_support_equal_voter_realization g hg e a b c hab hbc hstrength orders (twoTypeWeight theta)
    (twoTypeWeight_nonneg theta ht) (twoTypeWeight_total theta) hscore
    (binaryHeight h) (binaryHeight_nonneg h) ⟨h, by omega⟩ (by simp [binaryHeight]) lam hlam
  rw [hgap, hcost]
  apply (mul_lt_mul_iff_left₀ hden).mp
  have htheta : (R + delta) * theta = R := by dsimp [theta]; field_simp
  have hrest : (R + delta) * (1 - theta) = delta := by nlinarith [htheta]
  have he : (lam - (k : ℝ) / (h + z : ℕ)) * R < ((h : ℝ) / (h + z : ℕ)) * delta := hexcess
  calc
    lam * theta * (R + delta) = lam * R := by rw [mul_assoc, mul_comm theta, htheta]
    _ < R * ((k : ℝ) / (h + z : ℕ)) + delta * ((h : ℝ) / (h + z : ℕ)) := by nlinarith only [he]
    _ = (theta * ((k : ℝ) / (h + z : ℕ)) + (1 - theta) * ((h : ℝ) / (h + z : ℕ))) * (R + delta) := by
      calc
        _ = ((R + delta) * theta) * ((k : ℝ) / (h + z : ℕ)) +
            ((R + delta) * (1 - theta)) * ((h : ℝ) / (h + z : ℕ)) := by rw [htheta, hrest]
        _ = _ := by ring

end OptimalG
