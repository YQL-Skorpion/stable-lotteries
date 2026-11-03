import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The exact scalar coercivity inequality in Appendix B.4. -/
namespace OptimalG.Variational
open Set Real

noncomputable def transportEntropy (x : ℝ) : ℝ := x-1-log x
noncomputable def transportEntropyRemainder (x : ℝ) : ℝ :=
  transportEntropy x-(8:ℝ)/9*(x-1)^2/(x+1)

theorem transportEntropyRemainder_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt transportEntropyRemainder ((x-1)*(x-3)^2/(9*x*(x+1)^2)) x := by
  have hp : x+1 ≠ 0 := by linarith
  have hrat := ((((hasDerivAt_id x).sub_const 1).pow 2).const_mul ((8:ℝ)/9)).div
    ((hasDerivAt_id x).add_const 1) hp
  have hd := (((hasDerivAt_id x).sub_const 1).sub (Real.hasDerivAt_log hx.ne')).sub hrat
  change HasDerivAt transportEntropyRemainder
    ((1-x⁻¹)-(((8:ℝ)/9*(2*(x-1)^1*1))*(x+1)-(8:ℝ)/9*(x-1)^2*1)/(x+1)^2) x at hd
  have he : ((1-x⁻¹)-(((8:ℝ)/9*(2*(x-1)^1*1))*(x+1)-(8:ℝ)/9*(x-1)^2*1)/(x+1)^2) =
      (x-1)*(x-3)^2/(9*x*(x+1)^2) := by
    field_simp
    ring
  rwa [he] at hd

/-- The global quantitative inequality used for the variation penalty. -/
theorem transportEntropy_coercive {x : ℝ} (hx : 0 < x) :
    (8:ℝ)/9*(x-1)^2/(x+1) ≤ transportEntropy x := by
  have hzero : transportEntropyRemainder 1 = 0 := by norm_num [transportEntropyRemainder,transportEntropy]
  have hright : MonotoneOn transportEntropyRemainder (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
      (fun r hr => (transportEntropyRemainder_hasDerivAt (by have hh : (1:ℝ) ≤ r := hr; linarith : 0 < r)).continuousAt.continuousWithinAt)
      (fun r hr => (transportEntropyRemainder_hasDerivAt (by have hh : (1:ℝ) ≤ r := interior_subset hr; linarith : 0 < r)).differentiableAt.differentiableWithinAt)
    intro r hr
    have hr1 : 1 ≤ r := interior_subset hr
    have hr0 : 0 < r := by linarith
    rw [(transportEntropyRemainder_hasDerivAt hr0).deriv]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hr1) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) hr0.le) (sq_nonneg _))
  have hleft : AntitoneOn transportEntropyRemainder (Ioc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
      (fun r hr => (transportEntropyRemainder_hasDerivAt hr.1).continuousAt.continuousWithinAt)
      (fun r hr => (transportEntropyRemainder_hasDerivAt (interior_subset hr).1).differentiableAt.differentiableWithinAt)
    intro r hr
    have hr' : r ∈ Ioc 0 1 := interior_subset hr
    rw [(transportEntropyRemainder_hasDerivAt hr'.1).deriv]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr'.2) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) hr'.1.le) (sq_nonneg _))
  have hnonneg : 0 ≤ transportEntropyRemainder x := by
    by_cases hx1 : 1 ≤ x
    · simpa only [hzero] using hright (show (1:ℝ) ∈ Ici 1 by simp) hx1 hx1
    · simpa only [hzero] using hleft ⟨hx,(le_of_not_ge hx1)⟩ (show (1:ℝ) ∈ Ioc 0 1 by norm_num) (le_of_not_ge hx1)
  exact sub_nonneg.mp hnonneg

end OptimalG.Variational
