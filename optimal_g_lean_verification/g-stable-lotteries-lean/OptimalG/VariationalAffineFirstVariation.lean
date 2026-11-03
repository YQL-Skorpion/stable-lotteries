import OptimalG.VariationalAffineSolution
import OptimalG.VariationalAffineComparison

/-! An auxiliary affine ODE computes the actual weighted scalar first
variation. This is an integral identity, not a claim of parameter
 differentiability of an ODE solution. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter Real

 theorem affineReferenceSolution_terminal {a b : ℝ} {alpha beta : ℝ → ℝ}
    (hab : a ≤ b) (ha : IntervalIntegrable alpha volume a b) :
    affineReferenceSolution a 0 alpha beta b =
      ∫ s in a..b,exp (∫ t in s..b,alpha t)*beta s := by
  simp only [affineReferenceSolution,zero_add]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hab] at hs
  have ha1 : IntervalIntegrable alpha volume a s := ha.mono_set (by
    rw [uIcc_of_le hs.1,uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hs.2)
  have ha2 : IntervalIntegrable alpha volume s b := ha.mono_set (by
    rw [uIcc_of_le hs.2,uIcc_of_le hab]
    exact Icc_subset_Icc hs.1 le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals ha1 ha2
  dsimp only
  rw [← mul_assoc,← exp_add]
  congr 2
  linarith only [hadd]

 theorem affine_variation_of_constants_terminal {a b x0 : ℝ} {alpha beta V : ℝ → ℝ}
    (hab : a ≤ b) (ha : IntervalIntegrable alpha volume a b)
    (hb : IntervalIntegrable beta volume a b)
    (hV : AbsolutelyContinuousOnInterval V a b) (hinit : V a=0)
    (hder : ∀ᵐ r ∂volume.restrict (Icc a b),deriv V r=alpha r*V r+beta r) :
    (∫ s in a..b,exp (∫ t in s..b,alpha t)*beta s)/x0=V b/x0 := by
  have hA := affineReferenceSolution_AC (x0:=0) ha hb
  have hAd : ∀ᵐ r ∂volume.restrict (Icc a b),
      deriv (affineReferenceSolution a 0 alpha beta) r=
        alpha r*affineReferenceSolution a 0 alpha beta r+beta r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (affineReferenceSolution_hasDerivAt_ae (x0:=0) ha hb)] with r hr hd
    exact (hd (by simpa only [uIcc_of_le hab] using hr)).deriv
  have he := integrable_affine_ode_unique ha hV hA
    (hinit.trans (affineReferenceSolution_initial _ _ _ _).symm) hder hAd
  rw [← affineReferenceSolution_terminal hab ha,← he ⟨hab,le_rfl⟩]

 theorem affine_scalar_variation_identity {a b : ℝ} {alpha alphaS betaS Z V : ℝ → ℝ}
    (hab : a ≤ b) (ha : IntervalIntegrable alpha volume a b)
    (haS : IntervalIntegrable alphaS volume a b) (hbS : IntervalIntegrable betaS volume a b)
    (hZ : ContinuousOn Z (uIcc a b))
    (hV : AbsolutelyContinuousOnInterval V a b) (hinit : V a=0)
    (hder : ∀ᵐ r ∂volume.restrict (Icc a b),
      deriv V r=alpha r*V r+(alphaS r*Z r+betaS r)) :
    (∫ s in a..b,exp (∫ t in s..b,alpha t)*(alphaS s*Z s+betaS s)/Z b)=V b/Z b := by
  rw [intervalIntegral.integral_div]
  exact affine_variation_of_constants_terminal hab ha ((haS.mul_continuousOn hZ).add hbS)
    hV hinit hder

end OptimalG.Variational
