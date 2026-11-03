import OptimalG.VariationalTransportZeroTerms

/-! Separation of the actual logarithmic transport source into coefficient,
first-derivative, and entropy integrals. Each has its own exact pushforward. -/
namespace OptimalG.Variational
open Set MeasureTheory Real

variable {I : Type*} [Fintype I]

noncomputable def transportCoefficientSource (rho w0 : ℝ → ℝ) (a a0 : ℝ → I → ℝ)
    (delta : I → ℝ) (s : ℝ) : ℝ :=
  rho s*∑ i, referenceWeight (a0 s i) (delta i) (w0 s)*log (a s i/a0 s i)

noncomputable def transportDerivativeSource (rho w0 : ℝ → ℝ) (a0 xi : ℝ → I → ℝ)
    (delta : I → ℝ) (s : ℝ) : ℝ :=
  rho s*∑ i, referenceWeight (a0 s i) (delta i) (w0 s)*(xi s i-1)

noncomputable def transportEntropySource (rho w0 : ℝ → ℝ) (a0 xi : ℝ → I → ℝ)
    (delta : I → ℝ) (s : ℝ) : ℝ :=
  rho s*∑ i, referenceWeight (a0 s i) (delta i) (w0 s)*transportEntropy (xi s i)

 theorem transportLogSource_split (rho w0 : ℝ → ℝ) (a a0 xi : ℝ → I → ℝ)
    (delta : I → ℝ) (s : ℝ) :
    rho s*transportLogSource a a0 xi delta w0 s =
      transportCoefficientSource rho w0 a a0 delta s-
      transportDerivativeSource rho w0 a0 xi delta s+
      transportEntropySource rho w0 a0 xi delta s := by
  unfold transportLogSource transportCoefficientSource transportDerivativeSource transportEntropySource
  simp_rw [mul_add,mul_sub]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  ring

 theorem transportLogSource_intervalIntegrable {s0 s1 : ℝ} {rho w0 : ℝ → ℝ}
    {a a0 xi : ℝ → I → ℝ} {delta : I → ℝ}
    (hcoef : IntervalIntegrable (transportCoefficientSource rho w0 a a0 delta) volume s0 s1)
    (hderiv : IntervalIntegrable (transportDerivativeSource rho w0 a0 xi delta) volume s0 s1)
    (hent : IntervalIntegrable (transportEntropySource rho w0 a0 xi delta) volume s0 s1) :
    IntervalIntegrable (fun s => rho s*transportLogSource a a0 xi delta w0 s) volume s0 s1 := by
  simpa only [transportLogSource_split,Pi.add_apply,Pi.sub_apply] using (hcoef.sub hderiv).add hent

 theorem transportLogSource_integral_split {s0 s1 : ℝ} {rho w0 : ℝ → ℝ}
    {a a0 xi : ℝ → I → ℝ} {delta : I → ℝ}
    (hcoef : IntervalIntegrable (transportCoefficientSource rho w0 a a0 delta) volume s0 s1)
    (hderiv : IntervalIntegrable (transportDerivativeSource rho w0 a0 xi delta) volume s0 s1)
    (hent : IntervalIntegrable (transportEntropySource rho w0 a0 xi delta) volume s0 s1) :
    (∫ s in s0..s1, rho s*transportLogSource a a0 xi delta w0 s) =
      (∫ s in s0..s1, transportCoefficientSource rho w0 a a0 delta s)-
      (∫ s in s0..s1, transportDerivativeSource rho w0 a0 xi delta s)+
      (∫ s in s0..s1, transportEntropySource rho w0 a0 xi delta s) := by
  simp_rw [transportLogSource_split]
  have hsub : IntervalIntegrable (fun s => transportCoefficientSource rho w0 a a0 delta s-
      transportDerivativeSource rho w0 a0 xi delta s) volume s0 s1 := hcoef.sub hderiv
  rw [intervalIntegral.integral_add hsub hent,intervalIntegral.integral_sub hcoef hderiv]

 theorem logarithmic_transport_split {s0 s1 : ℝ} {a a0 xi : ℝ → I → ℝ}
    {delta : I → ℝ} {w w0 : ℝ → ℝ}
    (hinterval : s0 ≤ s1)
    (hw : AbsolutelyContinuousOnInterval w s0 s1)
    (hw0 : AbsolutelyContinuousOnInterval w0 s0 s1)
    (hpositive : ∀ᵐ s ∂volume.restrict (Icc s0 s1), ∀ i,
      ((a s i = 0 ∧ a0 s i = 0) ∨ (0 < a s i ∧ 0 < a0 s i)) ∧ 0 < xi s i)
    (hwd : ∀ᵐ s ∂volume.restrict (Icc s0 s1),
      (∑ i, a s i*exp (-delta i*w s)/xi s i) ≤ deriv w s)
    (hw0d : ∀ᵐ s ∂volume.restrict (Icc s0 s1),
      deriv w0 s = ∑ i, referenceWeight (a0 s i) (delta i) (w0 s))
    (hB : IntervalIntegrable (transportReferenceB a0 delta w0) volume s0 s1)
    (hcoef : IntervalIntegrable (transportCoefficientSource
      (referenceIntegratingFactor s0 s1 (transportReferenceB a0 delta w0)) w0 a a0 delta) volume s0 s1)
    (hderiv : IntervalIntegrable (transportDerivativeSource
      (referenceIntegratingFactor s0 s1 (transportReferenceB a0 delta w0)) w0 a0 xi delta) volume s0 s1)
    (hent : IntervalIntegrable (transportEntropySource
      (referenceIntegratingFactor s0 s1 (transportReferenceB a0 delta w0)) w0 a0 xi delta) volume s0 s1) :
    referenceIntegratingFactor s0 s1 (transportReferenceB a0 delta w0) s0*(w s0-w0 s0)+
      (∫ s in s0..s1, transportCoefficientSource
        (referenceIntegratingFactor s0 s1 (transportReferenceB a0 delta w0)) w0 a a0 delta s)-
      (∫ s in s0..s1, transportDerivativeSource
        (referenceIntegratingFactor s0 s1 (transportReferenceB a0 delta w0)) w0 a0 xi delta s)+
      (∫ s in s0..s1, transportEntropySource
        (referenceIntegratingFactor s0 s1 (transportReferenceB a0 delta w0)) w0 a0 xi delta s) ≤
      w s1-w0 s1 := by
  have h := actual_logarithmic_transport_zero hinterval hw hw0 hpositive hwd hw0d hB
    (transportLogSource_intervalIntegrable hcoef hderiv hent)
  rw [transportLogSource_integral_split hcoef hderiv hent] at h
  linarith only [h]

end OptimalG.Variational
