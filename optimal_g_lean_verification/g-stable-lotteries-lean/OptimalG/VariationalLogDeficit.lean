import OptimalG.VariationalTransportWeights

/-! The actual logarithmic change of the high-rank continuation. -/
namespace OptimalG.Variational
open Real

noncomputable def logDeficit (M S : ℝ) (Y z : ℝ → ℝ) (s : ℝ) : ℝ :=
  log (M-S-Y (z s))

 theorem logDeficit_hasDerivAt {M S s Yd j : ℝ} {Y z : ℝ → ℝ}
    (hY : HasDerivAt Y Yd (z s)) (hz : HasDerivAt z j s)
    (hZ : 0 < M-S-Y (z s)) :
    HasDerivAt (logDeficit M S Y z) (-j*Yd/(M-S-Y (z s))) s := by
  have h := ((hY.comp s hz).const_sub (M-S)).log hZ.ne'
  convert! h using 1 <;> simp only [Function.comp_apply] <;> ring

/-- A tested linear control gives the corresponding positive-coefficient
logarithmic differential lower bound. -/
theorem logDeficit_linear_control {Z j A B Yd : ℝ}
    (hZ : 0 < Z) (hj : 0 ≤ j) (hY : Yd ≤ -(A*Z+B)) :
    j*A+j*B/Z ≤ -j*Yd/Z := by
  have h := mul_le_mul_of_nonneg_left hY hj
  apply (le_div_iff₀ hZ).2
  have hcancel : j*B/Z*Z = j*B := div_mul_cancel₀ _ hZ.ne'
  nlinarith only [h,hcancel]

 theorem logDeficit_initial_gap {Z E : ℝ} (hZ : 0 < Z) (hE : 0 ≤ E) :
    log (Z+E)-log Z = log (1+E/Z) := by
  rw [← log_div (by positivity : Z+E ≠ 0) hZ.ne']
  congr 1
  field_simp

 theorem logDeficit_terminal_nonpos {Z Zend : ℝ} (hZ : 0 < Z) (hbound : Z ≤ Zend) :
    log Z-log Zend ≤ 0 := sub_nonpos.mpr (Real.log_le_log hZ hbound)

end OptimalG.Variational
