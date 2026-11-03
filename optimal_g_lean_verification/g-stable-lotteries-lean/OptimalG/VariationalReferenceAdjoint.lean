import OptimalG.VariationalAffineComparison
import OptimalG.VariationalLogRegularity

/-! Positivity and the exact adjoint identity for the linear reference flow.
In particular the initial deficit is retained in rho(a), rather than replaced
by an unsupported constant independent of that deficit. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter Real
open scoped Topology

 theorem affineReferenceSolution_pos {a b x0 : ℝ} {alpha beta : ℝ → ℝ}
    (ha : IntervalIntegrable alpha volume a b) (hb : IntervalIntegrable beta volume a b)
    (hx0 : 0 < x0)
    (hbeta : ∀ᵐ r ∂volume.restrict (Icc a b), 0 ≤ beta r) :
    ∀ t ∈ Icc a b, 0 < affineReferenceSolution a x0 alpha beta t := by
  intro t ht
  have hh : 0 ≤ ∫ s in a..t,exp (-(∫ r in a..s,alpha r))*beta s := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict ht.1
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc le_rfl ht.2) hbeta]
      with s hs
    exact mul_nonneg (exp_pos _).le hs
  exact mul_pos (exp_pos _) (by linarith : 0 < x0+∫ s in a..t,exp (-(∫ r in a..s,alpha r))*beta s)

 theorem affine_solution_log_identity {a b : ℝ} {alpha beta Z : ℝ → ℝ}
    (hab : a ≤ b) (ha : IntervalIntegrable alpha volume a b)
    (hb : IntervalIntegrable beta volume a b) (hZ : AbsolutelyContinuousOnInterval Z a b)
    (hpos : ∀ t ∈ Icc a b, 0 < Z t)
    (hder : ∀ᵐ t ∂volume.restrict (Icc a b), HasDerivAt Z (alpha t*Z t+beta t) t) :
    (∫ t in a..b, beta t/Z t) = log (Z b)-log (Z a)-(∫ t in a..b,alpha t) := by
  have hlog := absolutelyContinuous_log hZ (by simpa only [uIcc_of_le hab] using hpos)
  have hcont : ContinuousOn (fun t => (Z t)⁻¹) (uIcc a b) := by
    apply hZ.continuousOn.inv₀
    intro t ht
    exact ne_of_gt (hpos t (by simpa only [uIcc_of_le hab] using ht))
  have hB : IntervalIntegrable (fun t => beta t/Z t) volume a b := by
    simpa only [div_eq_mul_inv] using hb.mul_continuousOn hcont
  have heq : ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv (fun t => log (Z t)) t=alpha t+beta t/Z t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,hder] with t ht hd
    rw [(hd.log (ne_of_gt (hpos t ht))).deriv]
    field_simp [ne_of_gt (hpos t ht)]
    <;> ring
  have hi := intervalIntegral.integral_congr_ae_restrict (a:=a) (b:=b) (μ:=volume)
    (f:=fun t => deriv (fun t => log (Z t)) t) (g:=fun t => alpha t+beta t/Z t) (by
    rw [uIoc_of_le hab,restrict_Ioc_eq_restrict_Icc]
    filter_upwards [heq] with t ht
    exact ht)
  rw [hlog.integral_deriv_eq_sub,intervalIntegral.integral_add ha hB] at hi
  linarith

 theorem affine_solution_initial_adjoint {a b : ℝ} {alpha beta Z : ℝ → ℝ}
    (hab : a ≤ b) (ha : IntervalIntegrable alpha volume a b)
    (hb : IntervalIntegrable beta volume a b) (hZ : AbsolutelyContinuousOnInterval Z a b)
    (hpos : ∀ t ∈ Icc a b, 0 < Z t)
    (hder : ∀ᵐ t ∂volume.restrict (Icc a b), HasDerivAt Z (alpha t*Z t+beta t) t) :
    referenceIntegratingFactor a b (fun t => beta t/Z t) a =
      exp (∫ t in a..b,alpha t)*Z a/Z b := by
  have h := affine_solution_log_identity hab ha hb hZ hpos hder
  have hZa := hpos a ⟨le_rfl,hab⟩
  have hZb := hpos b ⟨hab,le_rfl⟩
  simp only [referenceIntegratingFactor,intervalIntegral.integral_same,zero_sub]
  rw [h]
  have he : -(log (Z b)-log (Z a)-(∫ t in a..b,alpha t)) =
      (∫ t in a..b,alpha t)+log (Z a)-log (Z b) := by ring
  rw [he,exp_sub,exp_add,exp_log hZa,exp_log hZb]

end OptimalG.Variational
