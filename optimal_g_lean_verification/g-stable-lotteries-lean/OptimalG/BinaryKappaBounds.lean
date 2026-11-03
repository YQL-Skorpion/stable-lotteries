import OptimalG.BinaryAreaBounds

/-! The affine tail majorant must be checked as a coupled expression.
Separate coefficient domination is unnecessarily strong and need not hold. -/
namespace OptimalG
open Set

/-- Two endpoint checks for the affine numerator imply its bound at every
intermediate width. No separate bound on the linear coefficient is required. -/
theorem binaryKappa_affine_majorant_of_endpoints {phi : ℝ→ℝ}
    {z Y H d width B C : ℝ}
    (hz : z≠1) (hd : d ∈ Ioo (0:ℝ) 1) (hw : 0<width) (hdw : d≤width)
    (htail : curvePrimitive phi (1-d)=tailPrimitive z Y H (1-d))
    (hB : tailBackwardSlope z Y H/2-1≤B)
    (hend : tailBackwardSlope z Y H/2-1-(tailBackwardCurvature z Y H/3)*width≤B-C*width) :
    binaryKappa phi d≤(B-C*d)/(1-d) := by
  rw [binaryKappa_polynomial hz hd.1.ne' (ne_of_lt hd.2) htail]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hd.2).le
  have h1 := mul_nonneg (sub_nonneg.mpr hdw) (sub_nonneg.mpr hB)
  have h2 := mul_nonneg hd.1.le (sub_nonneg.mpr hend)
  have hmul : 0≤width*(B-C*d-(tailBackwardSlope z Y H/2-1-
      (tailBackwardCurvature z Y H/3)*d)) := by nlinarith only [h1,h2]
  have hh := nonneg_of_mul_nonneg_right hmul hw
  linarith only [hh]

end OptimalG
