import OptimalG.MiddleRankConvexity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Calculus comparison used in C.15 and C.16, retaining actual endpoint
values and derivatives rather than treating a sampled curve as a solution. -/
namespace OptimalG
open Set

theorem barrier_comparison_of_second_derivatives {a b : ℝ}
    {Y T dY dT ddY ddT : ℝ → ℝ}
    (hY : ContinuousOn Y (Icc a b)) (hT : ContinuousOn T (Icc a b))
    (hdY : ContinuousOn dY (Icc a b)) (hdT : ContinuousOn dT (Icc a b))
    (hYd : ∀ r ∈ Ioo a b,HasDerivAt Y (dY r) r)
    (hTd : ∀ r ∈ Ioo a b,HasDerivAt T (dT r) r)
    (hdYd : ∀ r ∈ Ioo a b,HasDerivAt dY (ddY r) r)
    (hdTd : ∀ r ∈ Ioo a b,HasDerivAt dT (ddT r) r)
    (hcurvature : ∀ r ∈ Ioo a b,ddT r ≤ ddY r)
    (hvalue : T a ≤ Y a) (hslope : dT a ≤ dY a) :
    ∀ r ∈ Icc a b,T r ≤ Y r := by
  have hmonoSlope : MonotoneOn (fun r => dY r-dT r) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (hdY.sub hdT)
    · intro r hr
      rw [interior_Icc] at hr
      exact ((hdYd r hr).sub (hdTd r hr)).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      change deriv (dY-dT) r ≥ 0
      rw [((hdYd r hr).sub (hdTd r hr)).deriv]
      exact sub_nonneg.mpr (hcurvature r hr)
  have hslopeAll : ∀ r ∈ Icc a b,dT r ≤ dY r := by
    intro r hr
    have hh := hmonoSlope ⟨le_rfl,hr.1.trans hr.2⟩ hr hr.1
    dsimp only at hh
    linarith
  have hmono : MonotoneOn (fun r => Y r-T r) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (hY.sub hT)
    · intro r hr
      rw [interior_Icc] at hr
      exact ((hYd r hr).sub (hTd r hr)).differentiableAt.differentiableWithinAt
    · intro r hr
      have hr' := interior_subset hr
      rw [interior_Icc] at hr
      change deriv (Y-T) r ≥ 0
      rw [((hYd r hr).sub (hTd r hr)).deriv]
      exact sub_nonneg.mpr (hslopeAll r hr')
  intro r hr
  have hh := hmono ⟨le_rfl,hr.1.trans hr.2⟩ hr hr.1
  dsimp only at hh
  linarith

/-- A strict differential inequality integrated backward from a nonnegative
endpoint forces a strict positive gap everywhere before that endpoint. -/
theorem backward_strict_linear_comparison {a b alpha : ℝ} {e ed : ℝ → ℝ}
    (he : ContinuousOn e (Icc a b))
    (hed : ∀ r ∈ Ioo a b,HasDerivAt e (ed r) r)
    (hstrict : ∀ r ∈ Ioo a b,ed r < alpha*e r)
    (hend : 0 ≤ e b) : ∀ r ∈ Ico a b,0 < e r := by
  let w := fun r => Real.exp (-alpha*r)*e r
  have hd (r : ℝ) (hr : r ∈ Ioo a b) :
      HasDerivAt w (Real.exp (-alpha*r)*(ed r-alpha*e r)) r := by
    have hh := (((hasDerivAt_id r).const_mul (-alpha)).exp).mul (hed r hr)
    convert! hh using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hw : StrictAntiOn w (Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc a b) (by dsimp [w]; fun_prop)
    intro r hr
    rw [interior_Icc] at hr
    rw [(hd r hr).deriv]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (sub_neg.mpr (hstrict r hr))
  intro r hr
  have hwb : 0 ≤ w b := mul_nonneg (Real.exp_pos _).le hend
  have hwlt := hw ⟨hr.1,hr.2.le⟩ ⟨hr.1.trans hr.2.le,le_rfl⟩ hr.2
  exact pos_of_mul_pos_right (hwb.trans_lt hwlt) (Real.exp_pos _).le

end OptimalG
