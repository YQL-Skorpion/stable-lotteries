import OptimalG.Certificates.LayerInterpolation

/-! Exact interpolation and padding allowance for the static step size. -/
namespace OptimalG.Certificates

theorem static_coefficientField_interpolation_lower {L S z Y p h C dC a da t : ℝ}
    (hh : h∈Set.Icc 0 (3/10000:ℝ)) (ht : t∈Set.Icc 0 1)
    (ha : a≤3) (hda : |da|≤2) (hk : |z-p-L|≤1) :
    min (coefficientField L S z Y p C a)
      (coefficientField L S z Y (p+h) (C+dC) (a+da*h))-h^2 ≤
      coefficientField L S z Y (p+h*t) (C+dC*t) (a+da*h*t) := by
  have htprod : 0≤t*(1-t) := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  have htquarter : t*(1-t)≤1/4 := by nlinarith [sq_nonneg (t-1/2)]
  have hprod : |da*(z-p-L)|≤2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hda hk (abs_nonneg (z-p-L)) (by norm_num : (0:ℝ)≤2)]
  have hda' := (abs_le.mp hda)
  have hterm : da*h*(t+1)/2≤1/2 := by
    have h1 : da*h≤2*h := mul_le_mul_of_nonneg_right hda'.2 hh.1
    have h2 : da*h*(t+1)≤2*h*(t+1) := mul_le_mul_of_nonneg_right h1 (by linarith [ht.1])
    have h3 : 2*h*(t+1)≤4*h := by nlinarith [mul_nonneg hh.1 (sub_nonneg.mpr ht.2)]
    linarith [hh.2]
  have hbracket : a/2-da*(z-p-L)+da*h*(t+1)/2≤4 := by
    linarith [(abs_le.mp hprod).1]
  have herror : t*(1-t)*h^2*(a/2-da*(z-p-L)+da*h*(t+1)/2)≤h^2 := by
    have h1 := mul_le_mul_of_nonneg_left hbracket (mul_nonneg htprod (sq_nonneg h))
    have h2 := mul_le_mul_of_nonneg_right htquarter (sq_nonneg h)
    nlinarith only [h1,h2]
  have hmin0 := min_le_left (coefficientField L S z Y p C a)
    (coefficientField L S z Y (p+h) (C+dC) (a+da*h))
  have hmin1 := min_le_right (coefficientField L S z Y p C a)
    (coefficientField L S z Y (p+h) (C+dC) (a+da*h))
  have h0 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hmin0)
  have h1 := mul_nonneg ht.1 (sub_nonneg.mpr hmin1)
  have he := coefficientField_interpolation_identity L S z Y p h C dC a da t
  nlinarith only [herror,h0,h1,he]

/-- The entire interpolation and coefficient-padding loss fits the exact
penalty already subtracted in every high-trajectory node residual. -/
theorem static_coefficientField_padded_lower {L S z Y p h C dC a da t : ℝ}
    (hh : h∈Set.Icc 0 (3/10000:ℝ)) (ht : t∈Set.Icc 0 1)
    (ha : a≤3) (hda : |da|≤2) (hk : |z-p-L|≤1)
    (hU : z-L≤1/3) (hK : quadratic L (z-(p+h*t))-S-Y≤1/8) :
    min (coefficientField L S z Y p C a)
      (coefficientField L S z Y (p+h) (C+dC) (a+da*h))-(1/10000000:ℝ) ≤
      coefficientField L S z Y (p+h*t) (C+dC*t+1/200000000)
        (a+da*h*t+1/200000000) := by
  have hb := static_coefficientField_interpolation_lower hh ht ha hda hk (C:=C) (dC:=dC) (S:=S) (Y:=Y)
  have hs : h^2≤(3/10000:ℝ)^2 := by nlinarith [hh.1,hh.2]
  have he : coefficientField L S z Y (p+h*t) (C+dC*t+1/200000000)
      (a+da*h*t+1/200000000) = coefficientField L S z Y (p+h*t) (C+dC*t)
      (a+da*h*t)-(z-L+quadratic L (z-(p+h*t))-S-Y)/200000000 := by
    unfold coefficientField
    ring
  rw [he]
  linarith


end OptimalG.Certificates
