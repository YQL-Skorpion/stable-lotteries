import OptimalG.Certificates.ControlRatio

namespace OptimalG.Certificates.Control

/-- The ordering y≥p is essential to the sharp uniform state-slope bound. -/
theorem alphaNumerator_upper (L p x y A B : ℝ)
    (hL : Compact.LambdaRange L)
    (hp : p ∈ Set.Icc (0.25 : ℝ) 0.36)
    (hx : x ∈ Set.Icc (0.285 : ℝ) 0.38)
    (hy : y ∈ Set.Icc (0.285 : ℝ) 0.38) (hpy : p ≤ y)
    (hA0 : 0 ≤ A) (hA : A ≤ L-x) (hB0 : 0 ≤ B) (hB : B ≤ L-y) :
    alphaNumerator (2*L-x) (p+y-L) A B ≤ (0.562330 : ℝ)^2-0.285^2 := by
  have hLa : 0 ≤ L-0.285 := by linarith [hL.1]
  have hh : 0 ≤ 2*L-0.285 := by linarith [hL.1]
  have hBprod := mul_le_mul (show 2*L-x ≤ 2*L-0.285 by linarith [hx.1]) hB hB0 hh
  have hnum : alphaNumerator (2*L-x) (p+y-L) A B ≤ L^2-0.285^2 := by
    unfold alphaNumerator
    by_cases hk : 0 ≤ p+y-L
    · have hAprod := mul_le_mul_of_nonneg_left
        (show A ≤ L-0.285 by linarith [hA, hx.1]) hk
      by_cases hpa : p ≤ 0.285
      · have hp' := mul_le_mul_of_nonneg_right hpa hLa
        have hy' := mul_le_mul_of_nonneg_left hy.1 (show 0 ≤ L by linarith [hL.1])
        nlinarith
      · have hp' := mul_le_mul_of_nonneg_left (le_of_not_ge hpa)
          (show (0:ℝ) ≤ 0.285 by norm_num)
        have hy' := mul_le_mul_of_nonneg_left hpy (show 0 ≤ L by linarith [hL.1])
        nlinarith
    · have hAprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hk) hA0
      have hy' := mul_le_mul_of_nonneg_left
        (show L-y ≤ L-0.285 by linarith [hy.1]) hh
      have hfac := mul_nonpos_of_nonneg_of_nonpos hLa
        (show L-2*0.285 ≤ 0 by linarith [hL.2])
      nlinarith
  have hsq := mul_nonneg (show 0 ≤ 0.562330-L by linarith [hL.2])
    (show 0 ≤ 0.562330+L by linarith [hL.1])
  nlinarith

theorem alpha_lt (L p x y R P A B : ℝ)
    (hL : Compact.LambdaRange L)
    (hp : p ∈ Set.Icc (0.25 : ℝ) 0.36)
    (hx : x ∈ Set.Icc (0.285 : ℝ) 0.38)
    (hy : y ∈ Set.Icc (0.285 : ℝ) 0.38) (hpy : p ≤ y)
    (hA0 : 0 ≤ A) (hA : A ≤ L-x) (hB0 : 0 ≤ B) (hB : B ≤ L-y)
    (hD : 0.0519 < det (2*L-x) (p+y-L) R P) :
    alphaNumerator (2*L-x) (p+y-L) A B / det (2*L-x) (p+y-L) R P < 4.53 := by
  apply (div_lt_iff₀ (show 0 < det (2*L-x) (p+y-L) R P by linarith)).mpr
  have hn := alphaNumerator_upper L p x y A B hL hp hx hy hpy hA0 hA hB0 hB
  nlinarith

end OptimalG.Certificates.Control
