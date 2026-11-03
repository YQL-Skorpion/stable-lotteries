import OptimalG.VariationalTransportDeficit

/-! A rational lower bound for the retained logarithmic initial term gives
small-deficit estimates without an exponential numerical certificate. -/
namespace OptimalG.Variational
open Real

 theorem log_initial_deficit_lower {Z E : ℝ} (hZ : 0 < Z) (hE : 0 ≤ E) :
    E/(Z+E) ≤ log (1+E/Z) := by
  have hp : 0 < 1+E/Z := by positivity
  have hh := Real.one_sub_inv_le_log_of_pos hp
  have he : 1-(1+E/Z)⁻¹=E/(Z+E) := by
    field_simp [hZ.ne',hp.ne',ne_of_gt (add_pos_of_pos_of_nonneg hZ hE)]
    ring
  rwa [he] at hh

 theorem initial_log_deficit_rational_bound {rho Z E eps : ℝ}
    (hrho : 0 ≤ rho) (hZ : 0 < Z) (hE : 0 ≤ E) (heps : eps < rho)
    (hbound : rho*log (1+E/Z) ≤ eps) : E ≤ eps*Z/(rho-eps) := by
  have hh := (mul_le_mul_of_nonneg_left (log_initial_deficit_lower hZ hE) hrho).trans hbound
  rw [← mul_div_assoc] at hh
  have hm := (div_le_iff₀ (add_pos_of_pos_of_nonneg hZ hE)).mp hh
  apply (le_div_iff₀ (sub_pos.mpr heps)).mpr
  nlinarith only [hm]

 theorem initial_high_deficit_lt_6e8 {rho Z E : ℝ}
    (hrho : (0.07 : ℝ) ≤ rho) (hZ : 0 < Z) (hZmax : Z ≤ (0.00136 : ℝ))
    (hE : 0 ≤ E) (hbound : rho*log (1+E/Z) ≤ (0.0000030001 : ℝ)) :
    E < (0.00000006 : ℝ) := by
  have hh := (mul_le_mul_of_nonneg_left (log_initial_deficit_lower hZ hE)
    (show 0 ≤ rho by linarith)).trans hbound
  rw [← mul_div_assoc] at hh
  have hm := (div_le_iff₀ (add_pos_of_pos_of_nonneg hZ hE)).mp hh
  have hlow := mul_le_mul_of_nonneg_right hrho hE
  nlinarith only [hm,hlow,hZmax]

end OptimalG.Variational
