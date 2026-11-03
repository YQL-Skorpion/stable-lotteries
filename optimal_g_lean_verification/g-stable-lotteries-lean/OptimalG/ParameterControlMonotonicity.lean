import OptimalG.Certificates.Control

/-! Increasing the distortion parameter weakens every nonnegative-score
rational control. A finite algebraic identity avoids a numerical derivative premise. -/
namespace OptimalG.Certificates.Control

 theorem parameter_value_mono {U h k R P K A B delta : ℝ}
    (hD : 0 < det h k R P) (hR : 0 ≤ R) (hP : 0 ≤ P) (hK : 0 ≤ K)
    (hU : 0 ≤ U) (hhk : 0 ≤ h+2*k) (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 ≤ delta) :
    value U h k R P K A B ≤ value (U-delta) (h+2*delta) (k-delta) R P K A B := by
  have hsum : 0 ≤ 2*R+P := by positivity
  have hDnew : 0 < det (h+2*delta) (k-delta) R P := by
    have hh := mul_nonneg hd hsum
    unfold det at *
    nlinarith
  have hT : 0 ≤ det h k R P+(2*R+P)*U+(h+2*k)*K :=
    add_nonneg (add_nonneg hD.le (mul_nonneg hsum hU)) (mul_nonneg hhk hK)
  have hN : 0 ≤ R*A+P*B := add_nonneg (mul_nonneg hR hA) (mul_nonneg hP hB)
  have hprod := mul_nonneg hd (mul_nonneg hT hN)
  have he :
      -((U-delta)*(R*A+P*B)+K*alphaNumerator (h+2*delta) (k-delta) A B)*det h k R P-
      (-(U*(R*A+P*B)+K*alphaNumerator h k A B)*det (h+2*delta) (k-delta) R P) =
      delta*(det h k R P+(2*R+P)*U+(h+2*k)*K)*(R*A+P*B) := by
    unfold det alphaNumerator
    ring
  unfold value
  apply (div_le_div_iff₀ hD hDnew).mpr
  nlinarith only [he,hprod]

theorem parameter_clipped_mono {U h k R P K A B delta : ℝ}
    (hD : 0 < det h k R P) (hR : 0 ≤ R) (hP : 0 ≤ P) (hK : 0 ≤ K)
    (hU : 0 ≤ U) (hhk : 0 ≤ h+2*k) (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 ≤ delta) :
    min (-U) (value U h k R P K A B) ≤
      min (-(U-delta)) (value (U-delta) (h+2*delta) (k-delta) R P K A B) :=
  min_le_min (by linarith) (parameter_value_mono hD hR hP hK hU hhk hA hB hd)

end OptimalG.Certificates.Control
