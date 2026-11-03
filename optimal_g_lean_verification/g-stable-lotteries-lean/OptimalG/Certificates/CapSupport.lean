import OptimalG.Certificates.CapCubic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OptimalG.Certificates
open Set

theorem capSlope_hasDerivAt (L S r : ℝ) (hr : r≠1) :
    HasDerivAt (capSlope L S) (-2*L*S/(1-r)^3) r := by
  have hh : 1-r≠0 := sub_ne_zero.mpr (Ne.symm hr)
  have hd := (hasDerivAt_const r (L/2)).sub ((hasDerivAt_const r (L*S)).div
    (((hasDerivAt_const r 1).sub (hasDerivAt_id r)).pow 2) (pow_ne_zero _ hh))
  have he : 0-(0*(1-r)^2-L*S*(2*(1-r)^(2-1)*(0-1)))/((1-r)^2)^2=
      -2*L*S/(1-r)^3 := by field_simp; ring
  change HasDerivAt (capSlope L S)
    (0-(0*(1-r)^2-L*S*(2*(1-r)^(2-1)*(0-1)))/((1-r)^2)^2) r at hd
  rwa [he] at hd

theorem capSlope_derivative_lower {L S r : ℝ}
    (hL : L∈Icc (0.562:ℝ) 0.563) (hS : S∈Icc (0.023:ℝ) 0.024)
    (hr : r∈Icc (0.28:ℝ) 0.296) : -(0.1:ℝ)≤-2*L*S/(1-r)^3 := by
  have hd : 0<(1-r)^3 := pow_pos (by linarith [hr.2]) _
  have hpow : (0.704:ℝ)^3≤(1-r)^3 := pow_le_pow_left₀ (by norm_num) (by linarith [hr.2]) 3
  have hnum : L*S≤(0.563:ℝ)*0.024 := mul_le_mul hL.2 hS.2 (by linarith [hS.1]) (by norm_num)
  apply (le_div_iff₀ hd).mpr
  nlinarith only [hpow,hnum]

/-- Adding the small affine slope makes the cap score monotone on the entire
prefix range. This proves all prefix supports at once. -/
theorem capSlope_prefix_monotone {L S : ℝ}
    (hL : L∈Icc (0.562:ℝ) 0.563) (hS : S∈Icc (0.023:ℝ) 0.024) :
    MonotoneOn (fun r => capSlope L S r+0.1*r) (Icc (0.28:ℝ) 0.296) := by
  have hd (r : ℝ) (hr : r∈Icc (0.28:ℝ) 0.296) :
      HasDerivAt (fun r => capSlope L S r+0.1*r) (-2*L*S/(1-r)^3+0.1) r := by
    have hh : r≠1 := by linarith [hr.2]
    have h := (capSlope_hasDerivAt L S r hh).add ((hasDerivAt_id r).const_mul 0.1)
    change HasDerivAt (fun r => capSlope L S r+0.1*r) (-2*L*S/(1-r)^3+0.1*1) r at h
    rwa [mul_one] at h
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hd r (interior_subset hr)).hasDerivWithinAt)
  intro r hr
  linarith [capSlope_derivative_lower hL hS (interior_subset hr)]

theorem capSlope_prefix_support {L S c r d : ℝ}
    (hL : L∈Icc (0.562:ℝ) 0.563) (hS : S∈Icc (0.023:ℝ) 0.024)
    (hc : c∈Icc (0.28:ℝ) 0.296) (hr : r∈Icc (0.28:ℝ) c) (hd : d≤-(0.1:ℝ)) :
    capSlope L S r≤capSlope L S c+d*(r-c) := by
  have hm := capSlope_prefix_monotone hL hS ⟨hr.1,hr.2.trans hc.2⟩ hc hr.2
  have hp := mul_le_mul_of_nonpos_right hd (sub_nonpos.mpr hr.2)
  linarith

end OptimalG.Certificates
