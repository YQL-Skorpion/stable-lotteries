import OptimalG.Certificates.Control

/-! Raising the primitive mass weakens the clipped three-class control.
The comparison uses the line barrier and needs no sign assumption on the
control's state coefficient or on the second score. -/
namespace OptimalG.Certificates.Control

 theorem value_R_raise_clipped (U h k R R' P K A B : ℝ)
    (hD : 0 < det h k R P) (hR : R ≤ R')
    (hU : 0 ≤ U) (hh : 0 ≤ h) (hA : A ≤ h) :
    min (-U) (value U h k R P K A B) ≤ value U h k R' P K A B := by
  have hD' : 0 < det h k R' P := by
    have hi := mul_le_mul_of_nonneg_left hR hh
    unfold det at *
    linarith
  by_cases hline : value U h k R' P K A B ≤ -U
  · have hold := div_mul_cancel₀ (-(U*(R*A+P*B)+K*alphaNumerator h k A B)) hD.ne'
    have hnew := div_mul_cancel₀ (-(U*(R'*A+P*B)+K*alphaNumerator h k A B)) hD'.ne'
    change value U h k R P K A B*det h k R P= _ at hold
    change value U h k R' P K A B*det h k R' P= _ at hnew
    have hm := mul_le_mul_of_nonneg_left hline hh
    have ha := mul_nonneg hU (sub_nonneg.mpr hA)
    have hcoef : 0 ≤ -U*A-h*value U h k R' P K A B := by nlinarith only [hm,ha]
    have hprod := mul_nonneg (sub_nonneg.mpr hR) hcoef
    have he : (value U h k R' P K A B-value U h k R P K A B)*det h k R P =
        (R'-R)*(-U*A-h*value U h k R' P K A B) := by
      unfold det at hold hnew ⊢
      nlinarith only [hold,hnew]
    rw [← he] at hprod
    have hv : value U h k R P K A B ≤ value U h k R' P K A B := by
      have hi := (mul_nonneg_iff_of_pos_right hD).mp hprod
      linarith
    exact (min_le_right _ _).trans hv
  · exact (min_le_left _ _).trans (le_of_not_ge hline)

end OptimalG.Certificates.Control
