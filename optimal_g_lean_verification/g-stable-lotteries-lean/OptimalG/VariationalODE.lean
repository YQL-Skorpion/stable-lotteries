import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

/-!
# Scalar comparison for the continuation equation

The proof uses a strictly positive exponential barrier and then sends its
initial size to zero. It therefore applies to subsolutions and supersolutions,
including the comparisons with averaged controls in Appendix B.2.
-/

namespace OptimalG.Variational

open Set Real
open scoped NNReal

/-- Scalar ODE comparison with a uniformly Lipschitz vector field. -/
theorem scalar_ode_comparison
    (F : ℝ → ℝ → ℝ) (K : ℝ≥0)
    (x y xd yd : ℝ → ℝ) (a b : ℝ)
    (hF : ∀ t ∈ Ico a b, LipschitzWith K (F t))
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hxd : ∀ t ∈ Ico a b, HasDerivWithinAt x (xd t) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, HasDerivWithinAt y (yd t) (Ici t) t)
    (hsub : ∀ t ∈ Ico a b, xd t ≤ F t (x t))
    (hsuper : ∀ t ∈ Ico a b, F t (y t) ≤ yd t)
    (hinit : x a ≤ y a) :
    ∀ t ∈ Icc a b, x t ≤ y t := by
  have hbarrier : ∀ eps : ℝ, 0 < eps → ∀ t ∈ Icc a b,
      x t ≤ y t + gronwallBound eps ((K : ℝ) + 1) 0 (t - a) := by
    intro eps heps
    let e : ℝ → ℝ := fun t => gronwallBound eps ((K : ℝ) + 1) 0 (t - a)
    have hederiv (t : ℝ) : HasDerivAt e (((K : ℝ) + 1) * e t) t := by
      simpa [e] using hasDerivAt_gronwallBound_shift eps ((K : ℝ) + 1) 0 t a
    have hepos (t : ℝ) : 0 < e t := by
      dsimp [e]
      rw [gronwallBound_ε0]
      exact mul_pos heps (exp_pos _)
    have hecont : Continuous e := continuous_iff_continuousAt.mpr
      (fun t => (hederiv t).continuousAt)
    apply image_le_of_deriv_right_lt_deriv_boundary' hx hxd
      (B := fun t => y t + e t) (B' := fun t => yd t + ((K : ℝ) + 1) * e t)
    · have h := hepos a
      linarith
    · exact hy.add hecont.continuousOn
    · intro t ht
      exact (hyd t ht).add (hederiv t).hasDerivWithinAt
    · intro t ht hcross
      have hdist : dist (x t) (y t) = e t := by
        change x t = y t + e t at hcross
        rw [Real.dist_eq, hcross, add_sub_cancel_left, abs_of_pos (hepos t)]
      have hfield := (hF t ht).dist_le_mul (x t) (y t)
      rw [hdist, Real.dist_eq] at hfield
      have hfield' := (le_abs_self (F t (x t) - F t (y t))).trans hfield
      have h1 := hsub t ht
      have h2 := hsuper t ht
      have h3 := hepos t
      nlinarith
  intro t ht
  apply le_of_forall_pos_le_add
  intro delta hdelta
  let E := exp (((K : ℝ) + 1) * (t - a))
  have hE : 0 < E := exp_pos _
  have h := hbarrier (delta / E) (div_pos hdelta hE) t ht
  rw [gronwallBound_ε0] at h
  change x t ≤ y t + delta / E * E at h
  rwa [div_mul_cancel₀ delta (ne_of_gt hE)] at h

/-- Two solutions of the same scalar equation and initial value agree.
This is an order-theoretic consequence of comparison, without a further
regularity assumption on the time dependence. -/
theorem scalar_ode_unique
    (F : ℝ → ℝ → ℝ) (K : ℝ≥0) (x y : ℝ → ℝ) (a b : ℝ)
    (hF : ∀ t ∈ Ico a b, LipschitzWith K (F t))
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hxd : ∀ t ∈ Ico a b, HasDerivWithinAt x (F t (x t)) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, HasDerivWithinAt y (F t (y t)) (Ici t) t)
    (hinit : x a = y a) :
    EqOn x y (Icc a b) := by
  have hxy := scalar_ode_comparison F K x y (fun t => F t (x t))
    (fun t => F t (y t)) a b hF hx hy hxd hyd
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) hinit.le
  have hyx := scalar_ode_comparison F K y x (fun t => F t (y t))
    (fun t => F t (x t)) a b hF hy hx hyd hxd
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) hinit.ge
  exact fun t ht => le_antisymm (hxy t ht) (hyx t ht)

/-- A field lying between a trajectory's derivative and that derivative plus
epsilon has a trajectory within the explicit Gronwall error. This is the
quantitative approximation used by the tent-averaged controls. -/
theorem scalar_ode_approximation_gap
    (G : ℝ → ℝ → ℝ) (K : ℝ≥0) (x y xd : ℝ → ℝ) (a b eps : ℝ)
    (heps : 0 ≤ eps)
    (hG : ∀ t ∈ Ico a b, LipschitzWith K (G t))
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hxd : ∀ t ∈ Ico a b, HasDerivWithinAt x (xd t) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, HasDerivWithinAt y (G t (y t)) (Ici t) t)
    (hgap : ∀ t ∈ Ico a b, xd t ≤ G t (x t) ∧ G t (x t) ≤ xd t + eps)
    (hinit : x a = y a) :
    ∀ t ∈ Icc a b, x t ≤ y t ∧
      y t ≤ x t + gronwallBound 0 K eps (t - a) := by
  let e : ℝ → ℝ := fun t => gronwallBound 0 K eps (t - a)
  have he0 : e a = 0 := by simp [e, gronwallBound_x0]
  have hepos {t : ℝ} (ht : a ≤ t) : 0 ≤ e t := by
    have hm := gronwallBound_mono (δ := 0) (by norm_num) heps K.coe_nonneg
      (show 0 ≤ t - a by linarith)
    simpa only [gronwallBound_x0] using hm
  have hed (t : ℝ) : HasDerivAt e ((K : ℝ) * e t + eps) t :=
    hasDerivAt_gronwallBound_shift 0 K eps t a
  have hecont : Continuous e := continuous_iff_continuousAt.mpr
    (fun t => (hed t).continuousAt)
  have hlo := scalar_ode_comparison G K x y xd (fun t => G t (y t)) a b hG hx hy
    hxd hyd (fun t ht => (hgap t ht).1) (fun _ _ => le_rfl) hinit.le
  have hhi := scalar_ode_comparison G K y (fun t => x t + e t)
    (fun t => G t (y t)) (fun t => xd t + ((K : ℝ) * e t + eps)) a b hG hy
    (hx.add hecont.continuousOn) hyd
    (fun t ht => (hxd t ht).add (hed t).hasDerivWithinAt)
    (fun _ _ => le_rfl) (fun t ht => ?_) (by rw [he0, add_zero, hinit])
  · intro t ht
    exact ⟨hlo t ht, hhi t ht⟩
  · have hlip := (hG t ht).dist_le_mul (x t + e t) (x t)
    rw [Real.dist_eq, Real.dist_eq, add_sub_cancel_left,
      abs_of_nonneg (hepos ht.1)] at hlip
    have hh := (le_abs_self (G t (x t + e t) - G t (x t))).trans hlip
    linarith [(hgap t ht).2]

end OptimalG.Variational
