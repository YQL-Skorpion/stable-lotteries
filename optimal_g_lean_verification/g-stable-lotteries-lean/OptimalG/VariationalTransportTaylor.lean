import OptimalG.VariationalTransportWeights

/-! The second-order segment estimate used for the transported log
coefficients. Numeric Hessian enclosures enter only through the explicit
lower bound on the actual second derivative along the segment. -/
namespace OptimalG.Variational
open Set

 theorem segment_second_order_lower {f f' f'' : ℝ → ℝ} {c : ℝ}
    (hf : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f' (f'' t) t)
    (hsecond : ∀ t ∈ Ioo (0:ℝ) 1, c ≤ f'' t) :
    f 0+f' 0+c/2 ≤ f 1 := by
  let g := fun t => f' t-c*t
  have hgd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt g (f'' t-c) t := by
    convert! (hf' t ht).sub ((hasDerivAt_id t).const_mul c) using 1 <;> simp [g,Pi.sub_apply]
  have hgm : MonotoneOn g (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (hgd t ht).continuousAt.continuousWithinAt)
    · intro t ht
      exact (hgd t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact sub_nonneg.mpr (hsecond t ht)
  have hfirst (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : f' 0+c*t ≤ f' t := by
    have h := hgm (show (0:ℝ) ∈ Icc 0 1 by norm_num) ht ht.1
    dsimp [g] at h
    linarith
  let H := fun t => f t-f' 0*t-(c/2)*t^2
  have hHd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt H (f' t-f' 0-c*t) t := by
    have h := ((hf t ht).sub ((hasDerivAt_id t).const_mul (f' 0))).sub
      (((hasDerivAt_id t).pow 2).const_mul (c/2))
    convert! h using 1 <;> simp [H,Pi.sub_apply,Pi.pow_apply] <;> ring
  have hHm : MonotoneOn H (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (hHd t ht).continuousAt.continuousWithinAt)
    · intro t ht
      exact (hHd t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have hh := hfirst t (interior_subset ht)
      linarith
  have h := hHm (show (0:ℝ) ∈ Icc 0 1 by norm_num) (show (1:ℝ) ∈ Icc 0 1 by norm_num) (by norm_num)
  dsimp [H] at h
  nlinarith

end OptimalG.Variational
