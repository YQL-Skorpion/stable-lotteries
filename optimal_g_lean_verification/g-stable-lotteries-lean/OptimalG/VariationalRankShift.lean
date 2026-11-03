import OptimalG.Certificates.Control

/-! Exact rank and score replacement identities, equation (B.5). -/
namespace OptimalG.Certificates.Control

noncomputable def theta (h k R P A B : ℝ) : ℝ := (R*A+P*B)/det h k R P

theorem value_x_shift (U h k R P K A B dx dA : ℝ)
    (hD : det h k R P ≠ 0) (hD' : det (h-dx) k R P ≠ 0) :
    value U (h-dx) k R P K (A+dA) B - value U h k R P K A B =
      -cx U k R K / det (h-dx) k R P * (dA+theta h k R P A B*dx) := by
  unfold value theta
  field_simp
  unfold det cx alphaNumerator
  ring

theorem theta_x_shift (h k R P A B dx dA : ℝ)
    (hD : det h k R P ≠ 0) (hD' : det (h-dx) k R P ≠ 0) :
    theta (h-dx) k R P (A+dA) B - theta h k R P A B =
      R / det (h-dx) k R P * (dA+theta h k R P A B*dx) := by
  unfold theta
  field_simp
  unfold det
  ring

theorem value_y_shift (U h k R P K A B dy dB : ℝ)
    (hD : det h k R P ≠ 0) (hD' : det h (k+dy) R P ≠ 0) :
    value U h (k+dy) R P K A (B+dB) - value U h k R P K A B =
      -cy U h P K / det h (k+dy) R P * (dB+theta h k R P A B*dy) := by
  unfold value theta
  field_simp
  unfold det cy alphaNumerator
  ring

theorem theta_y_shift (h k R P A B dy dB : ℝ)
    (hD : det h k R P ≠ 0) (hD' : det h (k+dy) R P ≠ 0) :
    theta h (k+dy) R P A (B+dB) - theta h k R P A B =
      P / det h (k+dy) R P * (dB+theta h k R P A B*dy) := by
  unfold theta
  field_simp
  unfold det
  ring

theorem value_x_shift_nonincreasing (U h k R P K A B dx dA : ℝ)
    (hD : 0 < det h k R P) (hD' : 0 < det (h-dx) k R P)
    (hc : 0 ≤ cx U k R K) (hs : 0 ≤ dA+theta h k R P A B*dx) :
    value U (h-dx) k R P K (A+dA) B ≤ value U h k R P K A B := by
  apply sub_nonpos.mp
  rw [value_x_shift _ _ _ _ _ _ _ _ _ _ hD.ne' hD'.ne']
  exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) hD'.le) hs

theorem value_y_shift_nonincreasing (U h k R P K A B dy dB : ℝ)
    (hD : 0 < det h k R P) (hD' : 0 < det h (k+dy) R P)
    (hc : 0 ≤ cy U h P K) (hs : 0 ≤ dB+theta h k R P A B*dy) :
    value U h (k+dy) R P K A (B+dB) ≤ value U h k R P K A B := by
  apply sub_nonpos.mp
  rw [value_y_shift _ _ _ _ _ _ _ _ _ _ hD.ne' hD'.ne']
  exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) hD'.le) hs

theorem value_x_shift_order_iff (U h k R P K A B dx dA : ℝ)
    (hD : 0 < det h k R P) (hD' : 0 < det (h-dx) k R P)
    (hc : 0 < cx U k R K) :
    value U h k R P K A B ≤ value U (h-dx) k R P K (A+dA) B ↔
      dA+theta h k R P A B*dx ≤ 0 := by
  rw [← sub_nonneg,value_x_shift _ _ _ _ _ _ _ _ _ _ hD.ne' hD'.ne']
  have hneg := div_neg_of_neg_of_pos (neg_neg_of_pos hc) hD'
  constructor
  · intro hh
    nlinarith
  · intro hh
    exact mul_nonneg_of_nonpos_of_nonpos hneg.le hh

theorem value_y_shift_order_iff (U h k R P K A B dy dB : ℝ)
    (hD : 0 < det h k R P) (hD' : 0 < det h (k+dy) R P)
    (hc : 0 < cy U h P K) :
    value U h k R P K A B ≤ value U h (k+dy) R P K A (B+dB) ↔
      dB+theta h k R P A B*dy ≤ 0 := by
  rw [← sub_nonneg,value_y_shift _ _ _ _ _ _ _ _ _ _ hD.ne' hD'.ne']
  have hneg := div_neg_of_neg_of_pos (neg_neg_of_pos hc) hD'
  constructor
  · intro hh
    nlinarith
  · intro hh
    exact mul_nonneg_of_nonpos_of_nonpos hneg.le hh

theorem value_scoreB_difference (U h k R P K A B B' : ℝ) :
    value U h k R P K A B'-value U h k R P K A B =
      -cy U h P K / det h k R P * (B'-B) := by
  unfold value alphaNumerator cy
  ring

theorem value_scoreA_difference (U h k R P K A A' B : ℝ) :
    value U h k R P K A' B-value U h k R P K A B =
      -cx U k R K / det h k R P * (A'-A) := by
  unfold value alphaNumerator cx
  ring

end OptimalG.Certificates.Control
