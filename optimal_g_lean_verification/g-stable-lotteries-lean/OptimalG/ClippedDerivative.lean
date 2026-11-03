import OptimalG.VariationalODE

/-! A lower derivative bound on the active branch controls the clipped function. -/
namespace OptimalG
open Set

/-- Only derivatives below the clipping ceiling need to be bounded. The
comparison proof also covers crossings of the two branches. -/
theorem clipped_decrease_of_active_derivative
    (f fd : ℝ → ℝ) (a b C B : ℝ) (hB : 0 ≤ B)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt f (fd t) (Ici t) t)
    (hb : ∀ t ∈ Ico a b, f t ≤ C → -B ≤ fd t) :
    ∀ t ∈ Icc a b, min C (f a) - B * (t - a) ≤ min C (f t) := by
  let m := min C (f a)
  have heps (eps : ℝ) (heps : 0 < eps) :
      ∀ t ∈ Icc a b, -f t ≤ -m + B * (t - a) + eps * (1 + t - a) := by
    have hbar (t : ℝ) : HasDerivAt
        (fun t : ℝ => -m + B * (t - a) + eps * (1 + t - a)) (B + eps) t := by
      convert ((((hasDerivAt_id t).sub_const a).const_mul B).const_add (-m)).add
        ((((hasDerivAt_id t).const_add 1).sub_const a).const_mul eps) using 1 <;>
        first | rfl | (simp only [id_eq, mul_one] <;> ring)
    apply image_le_of_deriv_right_lt_deriv_boundary' hc.neg (fun t ht => (hd t ht).neg)
      (B := fun t => -m + B * (t - a) + eps * (1 + t - a)) (B' := fun _ => B + eps)
    · dsimp [m]
      have hm := min_le_right C (f a)
      nlinarith
    · exact (by fun_prop : Continuous (fun t : ℝ => -m + B * (t - a) + eps * (1 + t - a))).continuousOn
    · intro t ht
      exact (hbar t).hasDerivWithinAt
    · intro t ht heq
      have ht0 : 0 ≤ t - a := sub_nonneg.mpr ht.1
      have hfC : f t ≤ C := by
        have hBB := mul_nonneg hB ht0
        have he := mul_nonneg heps.le (show 0 ≤ 1 + t - a by linarith)
        have hmC : m ≤ C := min_le_left _ _
        change -f t = -m + B * (t - a) + eps * (1 + t - a) at heq
        linarith
      have hh := hb t ht hfC
      change -fd t < B + eps
      linarith
  intro t ht
  apply le_min
  · have hmC : m ≤ C := min_le_left _ _
    have hh := mul_nonneg hB (sub_nonneg.mpr ht.1)
    change m - B * (t - a) ≤ C
    linarith
  · have hfactor : 0 < 1 + t - a := by linarith [ht.1]
    have hlim : -f t ≤ -m + B * (t - a) := by
      apply le_of_forall_pos_le_add
      intro delta hdelta
      have hh := heps (delta / (1 + t - a)) (div_pos hdelta hfactor) t ht
      rwa [div_mul_cancel₀ _ (ne_of_gt hfactor)] at hh
    change m - B * (t - a) ≤ f t
    linarith

end OptimalG
