import OptimalG.Certificates.ExtendedLocalData.EZero
import OptimalG.Certificates.ExtendedLocalData.EMax

/-! The local selected-high comparison is certified on a whole parameter
box; there is no mesh interpolation of the actual continuation. -/
namespace OptimalG.Certificates.ExtendedLocalChecks
open Set ExtendedLocalExpressions

theorem localCore_neg {lam S p t z e : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (9/25:ℝ) (56233/100000)) (hz : z∈Icc (391/500:ℝ) (7/8))
    (ht : t∈Icc (1529/5000:ℝ) (9/25)) (he : e∈Icc (0:ℝ) (17/5000)) :
    localCore lam S p t z e<0 := by
  have hlo := ExtendedLocalData.EZero.numerator_pos hL hS hp hz ht
  have hhi := ExtendedLocalData.EMax.numerator_pos hL hS hp hz ht
  rw [ExtendedLocalData.EZero.expression_identity] at hlo
  rw [ExtendedLocalData.EMax.expression_identity] at hhi
  by_cases he0 : e=0
  · simpa only [he0] using (neg_pos.mp hlo)
  have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr he.2) (neg_pos.mp hlo).le
  have h2 := mul_neg_of_pos_of_neg (lt_of_le_of_ne he.1 (Ne.symm he0)) (neg_pos.mp hhi)
  have hh : (17/5000)*localCore lam S p t z e<0 := by
    rw [deficit_affine]
    linarith only [h1,h2]
  exact neg_of_mul_neg_right hh (by norm_num : (0:ℝ)≤17/5000)

end OptimalG.Certificates.ExtendedLocalChecks
