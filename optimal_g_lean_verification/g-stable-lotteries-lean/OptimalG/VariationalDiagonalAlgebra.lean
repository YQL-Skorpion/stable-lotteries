import OptimalG.VariationalCapAlgebra

/-! Exact differentiation algebra for the coupled boundary y=p, equation B.7. -/
namespace OptimalG.Certificates.Control

noncomputable def diagonalSlope (U h k R P K A B Pp Kp : ℝ) : ℝ :=
  alphaNumerator h k A B/det h k R P *
    (B-cx U k R K/cy U h P K*Pp-Kp*det h k R P/cy U h P K) -
    2*theta h k R P A B

noncomputable def diagonalDerivativeNumerator (U h k R P K A B v Pp Kp : ℝ) : ℝ :=
  -(U*(B*A+Pp*B+P*v)+Kp*alphaNumerator h k A B+K*(2*A+h*v))*det h k R P +
    (U*(R*A+P*B)+K*alphaNumerator h k A B)*(h*B-2*P-k*Pp)

theorem diagonalDerivativeNumerator_eq (U h k R P K A B v Pp Kp : ℝ) :
    diagonalDerivativeNumerator U h k R P K A B v Pp Kp =
      alphaNumerator h k A B*(cy U h P K*B-cx U k R K*Pp-Kp*det h k R P) -
        cy U h P K*(2*(R*A+P*B)+det h k R P*v) := by
  unfold diagonalDerivativeNumerator alphaNumerator det cx cy
  ring

theorem diagonalSlope_eq_fraction (U h k R P K A B Pp Kp : ℝ)
    (hD : det h k R P ≠ 0) (hC : cy U h P K ≠ 0) :
    diagonalSlope U h k R P K A B Pp Kp =
      (alphaNumerator h k A B*(cy U h P K*B-cx U k R K*Pp-Kp*det h k R P) -
        2*cy U h P K*(R*A+P*B))/(cy U h P K*det h k R P) := by
  unfold diagonalSlope theta
  field_simp <;> ring

theorem diagonal_derivative_zero_iff (U h k R P K A B v Pp Kp : ℝ)
    (hD : det h k R P ≠ 0) (hC : cy U h P K ≠ 0) :
    diagonalDerivativeNumerator U h k R P K A B v Pp Kp = 0 ↔
      v = diagonalSlope U h k R P K A B Pp Kp := by
  rw [diagonalDerivativeNumerator_eq,diagonalSlope_eq_fraction _ _ _ _ _ _ _ _ _ _ hD hC,
    eq_div_iff (mul_ne_zero hC hD)]
  constructor <;> intro hh <;> linear_combination -hh

end OptimalG.Certificates.Control
