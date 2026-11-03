import OptimalG.PhaseControlBounds

/-! The exact row linearization used by the universal finite LP certificate. -/
namespace OptimalG

/-- Lower bounds on the two primitive ratios can be substituted into a
three-class row. This is a finite algebraic argument and needs no differentiability. -/
theorem three_class_ratio_lower_row
    {L p a b U X Y x y A B C : ℝ}
    (hL : 0 < L) (hp : 0 < p) (ha : a < L) (hb : b < L)
    (hk : 0 ≤ p + b - L) (hU : 0 ≤ U)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxX : x ≤ X) (hyY : y ≤ Y)
    (hbinary : p * X ≤ L)
    (hA : A ≤ L - a) (hB : B ≤ L - b) (hC : C ≤ -U)
    (hrow : (U + (p + b - L) * Y) * A + (U * X + (2 * L - a) * Y) * B +
      ((2 * L - a) - (p + b - L) * X) * C ≤ 0) :
    (U + (p + b - L) * y) * A + (U * x + (2 * L - a) * y) * B +
      ((2 * L - a) - (p + b - L) * x) * C ≤ 0 := by
  let h := 2 * L - a
  let k := p + b - L
  let M := k * A + h * B
  have hh : 0 < h := by dsimp [h]; linarith
  have hk' : 0 ≤ k := hk
  have hY : 0 ≤ Y := hy.trans hyY
  have hX : 0 ≤ X := hx.trans hxX
  have hpx : p * x ≤ L := (mul_le_mul_of_nonneg_left hxX hp.le).trans hbinary
  have hD : 0 < h - k * X := by
    have hb' := mul_le_mul_of_nonneg_left hbinary hk
    have hpos1 := mul_pos hp (sub_pos.mpr ha)
    have hpos2 := mul_pos hL (sub_pos.mpr hb)
    change 0 < 2 * L - a - (p + b - L) * X
    nlinarith
  have hDx : 0 < h - k * x := by
    have hmul := mul_le_mul_of_nonneg_left hxX hk'
    linarith
  change (U + k * y) * A + (U * x + h * y) * B + (h - k * x) * C ≤ 0
  change (U + k * Y) * A + (U * X + h * Y) * B + (h - k * X) * C ≤ 0 at hrow
  by_cases hM : M ≤ 0
  · have hAa := mul_le_mul_of_nonneg_left hA hU
    have hBb := mul_le_mul_of_nonneg_left hB (mul_nonneg hU hx)
    have hCc := mul_le_mul_of_nonneg_left hC hDx.le
    have hM' := mul_nonpos_of_nonneg_of_nonpos hy hM
    have hbin := mul_nonpos_of_nonneg_of_nonpos hU (sub_nonpos.mpr hpx)
    dsimp [M, h, k] at *
    nlinarith
  · have hM0 : 0 ≤ M := (lt_of_not_ge hM).le
    have hprod := mul_nonneg hM0 (add_nonneg hU (mul_nonneg hk' hY))
    have hrowk := mul_nonpos_of_nonneg_of_nonpos hk' hrow
    have hcoef : 0 ≤ U * B - k * C := by
      apply nonneg_of_mul_nonneg_left (b := h - k * X) ?_ hD
      dsimp [M] at hprod
      nlinarith
    have htermx := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxX) hcoef
    have htermy := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hyY) hM0
    dsimp [M] at htermy
    nlinarith

end OptimalG
