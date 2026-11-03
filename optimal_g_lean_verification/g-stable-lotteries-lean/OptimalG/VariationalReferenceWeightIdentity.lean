import OptimalG.VariationalReferenceAdjoint
import OptimalG.VariationalAffineFirstVariation

/-! The logarithmic adjoint weights equal the actual affine-flow weights at
every time, not just at the initial endpoint. This identifies the scalar
first variation with the independently constructed auxiliary solution. -/
namespace OptimalG.Variational
open Set MeasureTheory Real

theorem affine_solution_adjoint_at {a b : ℝ} {alpha beta Z : ℝ → ℝ}
    (hab : a≤b) (ha : IntervalIntegrable alpha volume a b)
    (hb : IntervalIntegrable beta volume a b) (hZ : AbsolutelyContinuousOnInterval Z a b)
    (hpos : ∀ t∈Icc a b,0<Z t)
    (hder : ∀ᵐ t ∂volume.restrict (Icc a b),deriv Z t=alpha t*Z t+beta t)
    {s : ℝ} (hs : s∈Icc a b) :
    referenceIntegratingFactor a b (fun t => beta t/Z t) s=
      exp (∫ t in s..b,alpha t)*Z s/Z b := by
  have hcont : ContinuousOn (fun t => (Z t)⁻¹) (uIcc a b) := by
    apply hZ.continuousOn.inv₀
    intro t ht
    exact (hpos t (by simpa only [uIcc_of_le hab] using ht)).ne'
  have hB : IntervalIntegrable (fun t => beta t/Z t) volume a b := by
    simpa only [div_eq_mul_inv] using hb.mul_continuousOn hcont
  have hleft : uIcc a s⊆uIcc a b := by
    rw [uIcc_of_le hs.1,uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hs.2
  have hright : uIcc s b⊆uIcc a b := by
    rw [uIcc_of_le hs.2,uIcc_of_le hab]
    exact Icc_subset_Icc hs.1 le_rfl
  have hdiff : ∀ᵐ t ∂volume.restrict (Icc a b),DifferentiableAt ℝ Z t := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    simpa only [uIcc_of_le hab] using hZ.ae_differentiableAt
  have hZd : ∀ᵐ t ∂volume.restrict (Icc s b),HasDerivAt Z (alpha t*Z t+beta t) t := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hs.1 le_rfl) hder,
      ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hs.1 le_rfl) hdiff] with t ht hd
    simpa only [ht] using hd.hasDerivAt
  have hlog := affine_solution_log_identity hs.2 (ha.mono_set hright)
    (hb.mono_set hright) (hZ.mono hright)
    (fun t ht => hpos t ⟨hs.1.trans ht.1,ht.2⟩) hZd
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hB.mono_set hleft) (hB.mono_set hright)
  have he : (∫ t in a..s,beta t/Z t)-(∫ t in a..b,beta t/Z t)=
      (∫ t in s..b,alpha t)+log (Z s)-log (Z b) := by
    linarith only [hlog,hadd]
  rw [referenceIntegratingFactor,he,exp_sub,exp_add,
    exp_log (hpos s hs),exp_log (hpos b ⟨hab,le_rfl⟩)]

theorem reference_weighted_scalar_variation {a b : ℝ}
    {alpha beta alphaS betaS Z V : ℝ → ℝ}
    (hab : a≤b) (ha : IntervalIntegrable alpha volume a b)
    (hb : IntervalIntegrable beta volume a b)
    (haS : IntervalIntegrable alphaS volume a b) (hbS : IntervalIntegrable betaS volume a b)
    (hZ : AbsolutelyContinuousOnInterval Z a b) (hpos : ∀ t∈Icc a b,0<Z t)
    (hZd : ∀ᵐ t ∂volume.restrict (Icc a b),deriv Z t=alpha t*Z t+beta t)
    (hV : AbsolutelyContinuousOnInterval V a b) (hinit : V a=0)
    (hVd : ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv V t=alpha t*V t+(alphaS t*Z t+betaS t)) :
    (∫ t in a..b,referenceIntegratingFactor a b (fun s => beta s/Z s) t*
      (alphaS t+betaS t/Z t))=V b/Z b := by
  rw [←affine_scalar_variation_identity hab ha haS hbS hZ.continuousOn hV hinit hVd]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  dsimp only
  rw [affine_solution_adjoint_at hab ha hb hZ hpos hZd ht]
  field_simp [(hpos t ht).ne',(hpos b ⟨hab,le_rfl⟩).ne']
  <;> ring

end OptimalG.Variational
