import OptimalG.VariationalAffineSolution

/-! Comparison and uniqueness for integrable scalar affine reference ODEs.
The residual inequalities may hold only almost everywhere, so piecewise cubic
barriers and piecewise affine reference controls are covered directly. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

 theorem integrable_linear_differential_nonneg {a b : ℝ} {alpha d : ℝ → ℝ}
    (ha : IntervalIntegrable alpha volume a b)
    (hd : AbsolutelyContinuousOnInterval d a b) (hinit : 0 ≤ d a)
    (hder : ∀ᵐ r ∂volume.restrict (Icc a b), alpha r*d r ≤ deriv d r) :
    ∀ t ∈ Icc a b, 0 ≤ d t := by
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have husub : uIcc a t ⊆ uIcc a b := by
    simpa only [uIcc_of_le ht.1,uIcc_of_le (ht.1.trans ht.2)] using hsub
  have hh := actual_integrating_factor_entropy (B:=fun r => -alpha r) (G:=fun _ => 0)
    ht.1 (ha.neg.mono_set husub) (hd.mono husub) (by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hder] with r hr
      simpa only [neg_neg,add_zero] using hr) (by simp)
  simp only [mul_zero,intervalIntegral.integral_zero,add_zero] at hh
  exact (mul_nonneg (referenceIntegratingFactor_pos _ _ _ _).le hinit).trans hh

 theorem integrable_affine_ode_comparison {a b : ℝ} {alpha beta X Y : ℝ → ℝ}
    (ha : IntervalIntegrable alpha volume a b)
    (hX : AbsolutelyContinuousOnInterval X a b) (hY : AbsolutelyContinuousOnInterval Y a b)
    (hinit : X a ≤ Y a)
    (hXd : ∀ᵐ r ∂volume.restrict (Icc a b), deriv X r ≤ alpha r*X r+beta r)
    (hYd : ∀ᵐ r ∂volume.restrict (Icc a b), alpha r*Y r+beta r ≤ deriv Y r) :
    ∀ t ∈ Icc a b, X t ≤ Y t := by
  by_cases hab : a ≤ b
  · have hdiffX : ∀ᵐ r ∂volume.restrict (Icc a b), DifferentiableAt ℝ X r := by
      apply (ae_restrict_iff' measurableSet_Icc).mpr
      simpa only [uIcc_of_le hab] using hX.ae_differentiableAt
    have hdiffY : ∀ᵐ r ∂volume.restrict (Icc a b), DifferentiableAt ℝ Y r := by
      apply (ae_restrict_iff' measurableSet_Icc).mpr
      simpa only [uIcc_of_le hab] using hY.ae_differentiableAt
    have hder : ∀ᵐ r ∂volume.restrict (Icc a b),
        alpha r*(Y r-X r) ≤ deriv (fun r => Y r-X r) r := by
      filter_upwards [hXd,hYd,hdiffX,hdiffY] with r hx hy hdx hdy
      rw [deriv_fun_sub hdy hdx]
      nlinarith only [hx,hy]
    intro t ht
    have hh := integrable_linear_differential_nonneg ha (hY.sub hX) (sub_nonneg.mpr hinit) hder t ht
    exact sub_nonneg.mp hh
  · intro t ht
    exact (hab (ht.1.trans ht.2)).elim

 theorem integrable_affine_ode_unique {a b : ℝ} {alpha beta X Y : ℝ → ℝ}
    (ha : IntervalIntegrable alpha volume a b)
    (hX : AbsolutelyContinuousOnInterval X a b) (hY : AbsolutelyContinuousOnInterval Y a b)
    (hinit : X a=Y a)
    (hXd : ∀ᵐ r ∂volume.restrict (Icc a b), deriv X r=alpha r*X r+beta r)
    (hYd : ∀ᵐ r ∂volume.restrict (Icc a b), deriv Y r=alpha r*Y r+beta r) :
    EqOn X Y (Icc a b) := by
  have hXY := integrable_affine_ode_comparison ha hX hY hinit.le
    (hXd.mono fun _ h => h.le) (hYd.mono fun _ h => h.ge)
  have hYX := integrable_affine_ode_comparison ha hY hX hinit.ge
    (hYd.mono fun _ h => h.le) (hXd.mono fun _ h => h.ge)
  exact fun t ht => le_antisymm (hXY t ht) (hYX t ht)

end OptimalG.Variational
