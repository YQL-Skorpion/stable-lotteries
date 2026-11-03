import OptimalG.VariationalTransportWeights
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! Entropy comparison for the actual logarithmic continuation. Applying the
inequality to a supersolution avoids any auxiliary existence assumption for
an ODE with only measurable matched-rank coefficients. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter Real
open scoped Topology

noncomputable def referenceWeight (a0 delta w0 : ℝ) : ℝ := a0*exp (-delta*w0)

theorem reciprocal_coefficient_entropy {a a0 delta w w0 xi : ℝ}
    (ha : 0 < a) (ha0 : 0 < a0) (hxi : 0 < xi) :
    referenceWeight a0 delta w0*(log (a/a0)-delta*(w-w0)-(xi-1)+transportEntropy xi) ≤
      a*exp (-delta*w)/xi-referenceWeight a0 delta w0 := by
  let v := log (a/a0)-delta*(w-w0)
  have h := mul_le_mul_of_nonneg_left (reciprocal_exp_entropy (v:=v) hxi)
    (show 0 ≤ referenceWeight a0 delta w0 from (mul_pos ha0 (exp_pos _)).le)
  have he : referenceWeight a0 delta w0*exp v = a*exp (-delta*w) := by
    have hexp : exp v = (a/a0)*exp (-delta*(w-w0)) := by
      dsimp [v]
      rw [exp_sub,exp_log (div_pos ha ha0),neg_mul,exp_neg]
      rfl
    rw [hexp]
    calc
      referenceWeight a0 delta w0*((a/a0)*exp (-delta*(w-w0))) =
          (a0*(a/a0))*(exp (-delta*w0)*exp (-delta*(w-w0))) := by
        unfold referenceWeight
        ring
      _ = a*exp (-delta*w) := by
        rw [← exp_add]
        have haa : a0*(a/a0) = a := by field_simp
        rw [haa]
        congr 2
        ring
  have he' : referenceWeight a0 delta w0*(exp v/xi) = a*exp (-delta*w)/xi := by
    rw [← mul_div_assoc,he]
  dsimp [v] at h
  nlinarith only [h,he']

 theorem logarithmic_field_entropy {I : Type*} [Fintype I]
    {a a0 delta xi : I → ℝ} {w w0 wd w0d : ℝ}
    (ha : ∀ i, 0 < a i) (ha0 : ∀ i, 0 < a0 i) (hxi : ∀ i, 0 < xi i)
    (hwd : (∑ i, a i*exp (-delta i*w)/xi i) ≤ wd)
    (hw0d : w0d = ∑ i, referenceWeight (a0 i) (delta i) w0) :
    -(∑ i, delta i*referenceWeight (a0 i) (delta i) w0)*(w-w0)+
      (∑ i, referenceWeight (a0 i) (delta i) w0*
        (log (a i/a0 i)-(xi i-1)+transportEntropy (xi i))) ≤ wd-w0d := by
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    reciprocal_coefficient_entropy (delta:=delta i) (w:=w) (w0:=w0) (ha i) (ha0 i) (hxi i))
  have hright : (∑ i, (a i*exp (-delta i*w)/xi i-referenceWeight (a0 i) (delta i) w0)) ≤ wd-w0d := by
    rw [Finset.sum_sub_distrib,← hw0d]
    exact sub_le_sub_right hwd w0d
  apply le_trans _ (hsum.trans hright)
  have he : -(∑ i, delta i*referenceWeight (a0 i) (delta i) w0)*(w-w0)+
      (∑ i, referenceWeight (a0 i) (delta i) w0*
        (log (a i/a0 i)-(xi i-1)+transportEntropy (xi i))) =
      ∑ i, referenceWeight (a0 i) (delta i) w0*
        (log (a i/a0 i)-delta i*(w-w0)-(xi i-1)+transportEntropy (xi i)) := by
    rw [neg_mul,Finset.sum_mul,← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  exact he.le

/-- Integrating the comparison with rho'=B rho removes the linear state
term. The explicit initial term is useful for deficit localization. -/
theorem integrating_factor_entropy {a b : ℝ} {rho d B G : ℝ → ℝ}
    (hab : a ≤ b)
    (hrho : AbsolutelyContinuousOnInterval rho a b)
    (hd : AbsolutelyContinuousOnInterval d a b)
    (hrhopos : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ rho t)
    (hrhod : ∀ᵐ t ∂volume.restrict (Icc a b), deriv rho t = B t*rho t)
    (hdd : ∀ᵐ t ∂volume.restrict (Icc a b), -B t*d t+G t ≤ deriv d t)
    (hG : IntervalIntegrable (fun t => rho t*G t) volume a b)
    (hend : rho b = 1) :
    rho a*d a+(∫ t in a..b, rho t*G t) ≤ d b := by
  have hprod : AbsolutelyContinuousOnInterval (fun t => rho t*d t) a b := hrho.mul hd
  have hdiffR : ∀ᵐ t ∂volume.restrict (Icc a b), DifferentiableAt ℝ rho t := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    simpa only [uIcc_of_le hab] using hrho.ae_differentiableAt
  have hdiffD : ∀ᵐ t ∂volume.restrict (Icc a b), DifferentiableAt ℝ d t := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    simpa only [uIcc_of_le hab] using hd.ae_differentiableAt
  have hae : ∀ᵐ t ∂volume.restrict (Icc a b), rho t*G t ≤ deriv (fun t => rho t*d t) t := by
    filter_upwards [hrhopos,hrhod,hdd,hdiffR,hdiffD] with t hp hrd hdd hR hD
    rw [deriv_fun_mul hR hD,hrd]
    nlinarith only [mul_le_mul_of_nonneg_left hdd hp]
  have hi := intervalIntegral.integral_mono_ae_restrict hab hG hprod.intervalIntegrable_deriv hae
  rw [hprod.integral_deriv_eq_sub,hend,one_mul] at hi
  linarith

end OptimalG.Variational
