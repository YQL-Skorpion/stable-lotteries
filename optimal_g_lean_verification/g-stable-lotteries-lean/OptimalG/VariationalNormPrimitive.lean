import OptimalG.VariationalNormLimit

/-! Strong score convergence automatically gives uniform primitive convergence. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

theorem lowPrimitive_tendstoUniformly_of_strong_data
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hphi : AENormTendsto (fun n => (dn n).phi) d.phi (volume.restrict (Icc ell tEnd))) :
    TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop := by
  obtain ⟨e, he, heb⟩ := hphi
  have hc : Tendsto (fun n => cap (lamn n) (dn n).S ell) atTop (𝓝 (cap lam d.S ell)) :=
    (((hlam.pow 2).sub (hlam.div_const 2)).add ((hlam.mul_const ell).div_const 2)).sub
      ((hlam.mul hS).div_const (1-ell))
  have herr : Tendsto (fun n => |cap (lamn n) (dn n).S ell-cap lam d.S ell|+e n*(tEnd-ell))
      atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, zero_mul, add_zero] using
      (hc.sub_const (cap lam d.S ell)).abs.add (he.mul_const (tEnd-ell))
  rw [Metric.tendstoUniformly_iff]
  intro eps heps
  filter_upwards [(tendsto_order.mp herr).2 eps heps] with n hnerr
  intro r
  have hscore : ∀ᵐ x ∂volume, x ∈ Icc ell tEnd → |(dn n).phi x-d.phi x| ≤ e n :=
    (ae_restrict_iff' measurableSet_Icc).mp (heb n).2
  have hi : |∫ x in ell..r, (dn n).phi x-d.phi x| ≤ e n * |(r:ℝ)-ell| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
    filter_upwards [hscore] with x hx
    intro hxr
    have hxI : x ∈ Icc ell tEnd := by
      have hxc : x ∈ Icc ell (r : ℝ) := by
        simpa only [uIcc_of_le r.property.1] using uIoc_subset_uIcc hxr
      exact ⟨hxc.1, hxc.2.trans r.property.2⟩
    simpa only [Real.norm_eq_abs] using hx hxI
  have hi' : |∫ x in ell..r, (dn n).phi x-d.phi x| ≤ e n * (tEnd-ell) := by
    apply hi.trans
    apply mul_le_mul_of_nonneg_left _ (heb n).1
    rw [abs_of_nonneg (sub_nonneg.mpr r.property.1)]
    linarith [r.property.2]
  have hnint := (hn n).intervalIntegrable le_rfl r.property.1 r.property.2
  have hdint := hd.intervalIntegrable le_rfl r.property.1 r.property.2
  change dist (lowPrimitive lam d r) (lowPrimitive (lamn n) (dn n) r) < eps
  rw [dist_comm, Real.dist_eq]
  apply lt_of_le_of_lt _ hnerr
  unfold lowPrimitive
  have heq : (cap (lamn n) (dn n).S ell+∫ x in ell..r,(dn n).phi x)-
      (cap lam d.S ell+∫ x in ell..r,d.phi x) =
      (cap (lamn n) (dn n).S ell-cap lam d.S ell)+
        ∫ x in ell..r,((dn n).phi x-d.phi x) := by
    rw [intervalIntegral.integral_sub hnint hdint]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add le_rfl hi')

end OptimalG.Variational
