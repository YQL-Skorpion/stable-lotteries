import OptimalG.Certificates.ReferenceFlowComparison

/-! A certified auxiliary affine solution supplies the scalar first variation.
Its polynomial residual uses the enclosed reference cubic X; the explicit
alphaS error term transfers this bound to the actual reference solution Z. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

theorem reference_sensitivity_enclosed {a b : ℝ}
    {alpha alphaS betaS X Z V Y Y' : ℝ→ℝ}
    (hlen : b-a≤2/25)
    (ha : IntervalIntegrable alpha volume a b)
    (hYder : ∀ t,HasDerivAt Y (Y' t) t) (hYcont : Continuous Y')
    (hV : AbsolutelyContinuousOnInterval V a b) (hinit : Y a=V a)
    (hVd : ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv V t=alpha t*V t+(alphaS t*Z t+betaS t))
    (hAlpha : ∀ᵐ t ∂volume.restrict (Icc a b),alpha t≤3)
    (hAlphaS : ∀ᵐ t ∂volume.restrict (Icc a b),|alphaS t|≤1000)
    (hZ : ∀ t∈Icc a b,|Z t-X t|≤(t-a)/2500000000)
    (hResidual : ∀ᵐ t ∂volume.restrict (Icc a b),
      |Y' t-alpha t*Y t-alphaS t*X t-betaS t|≤1/400000) :
    ∀ t∈Icc a b,|V t-Y t|≤(t-a)/250000 := by
  have hr : ∀ᵐ t ∂volume.restrict (Icc a b),
      |Y' t-alpha t*Y t-(alphaS t*Z t+betaS t)|≤3/1000000 := by
    filter_upwards [hResidual,hAlphaS,self_mem_ae_restrict measurableSet_Icc] with t he hs ht
    have hz := hZ t ht
    have hz' : |X t-Z t|≤(t-a)/2500000000 := by simpa only [abs_sub_comm] using hz
    have hprod := mul_le_mul hs hz' (abs_nonneg _) (by norm_num : (0:ℝ)≤1000)
    have hsum := abs_add_le (Y' t-alpha t*Y t-alphaS t*X t-betaS t)
      (alphaS t*(X t-Z t))
    rw [abs_mul] at hsum
    have hid : Y' t-alpha t*Y t-(alphaS t*Z t+betaS t)=
        (Y' t-alpha t*Y t-alphaS t*X t-betaS t)+alphaS t*(X t-Z t) := by ring
    rw [hid]
    have htime : t-a≤2/25 := (sub_le_sub_right ht.2 a).trans hlen
    linarith
  have h := affine_flow_enclosed_by_residual (A:=3) (eta:=3/1000000)
    (delta:=1/250000) (beta:=fun t => alphaS t*Z t+betaS t)
    (by norm_num) (by norm_num) (by nlinarith) ha hYder hYcont hV hinit hVd hAlpha hr
  simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using h

end OptimalG.Certificates.Transport
