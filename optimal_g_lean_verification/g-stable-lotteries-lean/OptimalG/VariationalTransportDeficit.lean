import OptimalG.VariationalTransportWeights

/-! Retaining the initial term in the direct logarithmic comparison gives an
explicit bound for the initial high-rank deficit. -/
namespace OptimalG.Variational
open Real

 theorem initial_log_deficit_nonneg {rho Z E : ℝ} (hrho : 0 ≤ rho) (hZ : 0 < Z) (hE : 0 ≤ E) :
    0 ≤ rho*log (1+E/Z) := by
  have hz : 1 ≤ 1+E/Z := le_add_of_nonneg_right (div_nonneg hE hZ.le)
  exact mul_nonneg hrho (Real.log_nonneg hz)

 theorem initial_log_deficit_bound {rho Z E eps : ℝ}
    (hrho : 0 < rho) (hZ : 0 < Z) (hE : 0 ≤ E)
    (hbound : rho*log (1+E/Z) ≤ eps) :
    E ≤ Z*(exp (eps/rho)-1) := by
  have hlog : log (1+E/Z) ≤ eps/rho :=
    (le_div_iff₀ hrho).2 (by simpa only [mul_comm] using hbound)
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by positivity : 0 < 1+E/Z)] at he
  have hm := mul_le_mul_of_nonneg_right he hZ.le
  rw [add_mul,div_mul_cancel₀ _ hZ.ne'] at hm
  nlinarith only [hm]

 theorem initial_log_deficit_of_transport {rho Z E base Lambda : ℝ}
    (hrho : 0 < rho) (hZ : 0 < Z) (hE : 0 ≤ E)
    (htransport : base+rho*log (1+E/Z) ≤ Lambda) (hfeasible : Lambda ≤ 0) :
    E ≤ Z*(exp ((-base)/rho)-1) := by
  exact initial_log_deficit_bound hrho hZ hE (by linarith)

end OptimalG.Variational
