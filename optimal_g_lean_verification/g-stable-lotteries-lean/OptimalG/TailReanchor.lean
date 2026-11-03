import OptimalG.PolynomialCompletion

/-! A fixed anchor represents the same terminal polynomial even when it
precedes the true join. The anchor values are polynomial extrapolations. -/
namespace OptimalG
open Set

theorem tailBackwardCoefficients_from_polynomial {a v g : ℝ} (ha : a≠1) :
    tailBackwardSlope a ((1-a)-v/2*(1-a)^2+g/3*(1-a)^3)
      (-1+v*(1-a)-g*(1-a)^2)=v ∧
    tailBackwardCurvature a ((1-a)-v/2*(1-a)^2+g/3*(1-a)^3)
      (-1+v*(1-a)-g*(1-a)^2)=g := by
  have hh : 1-a≠0 := sub_ne_zero.mpr ha.symm
  unfold tailBackwardSlope tailBackwardCurvature tailOne tailTwo
  constructor <;> field_simp [hh] <;> ring

theorem tailBackwardCoefficients_reanchor {a z Y H : ℝ} (ha : a≠1) (hz : z≠1) :
    tailBackwardSlope a (tailPrimitive z Y H a) (tailScore z Y H a)=tailBackwardSlope z Y H ∧
    tailBackwardCurvature a (tailPrimitive z Y H a) (tailScore z Y H a)=tailBackwardCurvature z Y H := by
  rw [tailPrimitive_backward z Y H a hz,tailScore_backward z Y H a hz]
  exact tailBackwardCoefficients_from_polynomial ha

theorem tailScore_reanchor {a z Y H : ℝ} (ha : a≠1) (hz : z≠1) (r : ℝ) :
    tailScore a (tailPrimitive z Y H a) (tailScore z Y H a) r=tailScore z Y H r := by
  rw [tailScore_backward a (tailPrimitive z Y H a) (tailScore z Y H a) r ha,
    (tailBackwardCoefficients_reanchor ha hz).1,(tailBackwardCoefficients_reanchor ha hz).2]
  exact (tailScore_backward z Y H r hz).symm

theorem tailPrimitive_reanchor {a z Y H : ℝ} (ha : a≠1) (hz : z≠1) (r : ℝ) :
    tailPrimitive a (tailPrimitive z Y H a) (tailScore z Y H a) r=tailPrimitive z Y H r := by
  rw [tailPrimitive_backward a (tailPrimitive z Y H a) (tailScore z Y H a) r ha,
    (tailBackwardCoefficients_reanchor ha hz).1,(tailBackwardCoefficients_reanchor ha hz).2]
  exact (tailPrimitive_backward z Y H r hz).symm

theorem tailPrimitive_anchor_linear {a Y H r : ℝ} (ha : a≠1) :
    tailPrimitive a Y H r=
      Y*((1-r)/(1-a))^2*(3-2*((1-r)/(1-a)))+
      (1-a)*H*((1-r)/(1-a))^2*(1-((1-r)/(1-a)))+
      (1-a)*((1-r)/(1-a))*(1-((1-r)/(1-a)))^2 := by
  have hh : 1-a≠0 := sub_ne_zero.mpr ha.symm
  rw [tailPrimitive_backward _ _ _ _ ha]
  unfold tailBackwardSlope tailBackwardCurvature tailOne tailTwo
  field_simp [hh]
  ring

theorem tailPrimitive_mono_anchor {a Ylo Yhi Hlo Hhi r : ℝ}
    (ha : a<1) (hr : r∈Icc a 1) (hY : Ylo≤Yhi) (hH : Hlo≤Hhi) :
    tailPrimitive a Ylo Hlo r≤tailPrimitive a Yhi Hhi r := by
  have hh : 0 < 1-a := sub_pos.mpr ha
  have hx : (1-r)/(1-a)∈Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hr.2) hh.le
    · exact (div_le_one hh).mpr (by linarith only [hr.1])
  have hfactorY : 0≤((1-r)/(1-a))^2*(3-2*((1-r)/(1-a))) :=
    mul_nonneg (sq_nonneg _) (by linarith only [hx.2])
  have hfactorH : 0≤(1-a)*((1-r)/(1-a))^2*(1-((1-r)/(1-a))) :=
    mul_nonneg (mul_nonneg hh.le (sq_nonneg _)) (sub_nonneg.mpr hx.2)
  have h1 := mul_le_mul_of_nonneg_right hY hfactorY
  have h2 := mul_le_mul_of_nonneg_right hH hfactorH
  rw [tailPrimitive_anchor_linear ha.ne,tailPrimitive_anchor_linear ha.ne]
  nlinarith only [h1,h2]

end OptimalG
