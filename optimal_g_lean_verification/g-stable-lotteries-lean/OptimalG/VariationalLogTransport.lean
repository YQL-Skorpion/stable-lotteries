import OptimalG.VariationalIntegratingFactor

/-! Integrated logarithmic transport for an actual absolutely continuous
competitor. Only its differential inequality is needed; no auxiliary ODE
solution with measurable coefficients is postulated. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter Real

variable {I : Type*} [Fintype I]

noncomputable def transportReferenceB (a0 : ℝ → I → ℝ) (delta : I → ℝ)
    (w0 : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∑ i, delta i*referenceWeight (a0 s i) (delta i) (w0 s)

noncomputable def transportLogSource (a a0 xi : ℝ → I → ℝ) (delta : I → ℝ)
    (w0 : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∑ i, referenceWeight (a0 s i) (delta i) (w0 s)*
    (log (a s i/a0 s i)-(xi s i-1)+transportEntropy (xi s i))

 theorem actual_logarithmic_transport {s0 s1 : ℝ} {a a0 xi : ℝ → I → ℝ}
    {delta : I → ℝ} {w w0 : ℝ → ℝ}
    (hinterval : s0 ≤ s1)
    (hw : AbsolutelyContinuousOnInterval w s0 s1)
    (hw0 : AbsolutelyContinuousOnInterval w0 s0 s1)
    (hpositive : ∀ᵐ s ∂volume.restrict (Icc s0 s1), ∀ i, 0 < a s i ∧ 0 < a0 s i ∧ 0 < xi s i)
    (hwd : ∀ᵐ s ∂volume.restrict (Icc s0 s1),
      (∑ i, a s i*exp (-delta i*w s)/xi s i) ≤ deriv w s)
    (hw0d : ∀ᵐ s ∂volume.restrict (Icc s0 s1),
      deriv w0 s = ∑ i, referenceWeight (a0 s i) (delta i) (w0 s))
    (hB : IntervalIntegrable (transportReferenceB a0 delta w0) volume s0 s1)
    (hsource : IntervalIntegrable (fun s => referenceIntegratingFactor s0 s1
      (transportReferenceB a0 delta w0) s*transportLogSource a a0 xi delta w0 s) volume s0 s1) :
    referenceIntegratingFactor s0 s1 (transportReferenceB a0 delta w0) s0*(w s0-w0 s0)+
      (∫ s in s0..s1, referenceIntegratingFactor s0 s1 (transportReferenceB a0 delta w0) s*
        transportLogSource a a0 xi delta w0 s) ≤ w s1-w0 s1 := by
  apply actual_integrating_factor_entropy hinterval hB (hw.sub hw0) _ hsource
  have hdiffw : ∀ᵐ s ∂volume.restrict (Icc s0 s1), DifferentiableAt ℝ w s := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    simpa only [uIcc_of_le hinterval] using hw.ae_differentiableAt
  have hdiffw0 : ∀ᵐ s ∂volume.restrict (Icc s0 s1), DifferentiableAt ℝ w0 s := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    simpa only [uIcc_of_le hinterval] using hw0.ae_differentiableAt
  filter_upwards [hpositive,hwd,hw0d,hdiffw,hdiffw0] with s hp hd hd0 hws hw0s
  rw [deriv_sub hws hw0s]
  exact logarithmic_field_entropy (fun i => (hp i).1) (fun i => (hp i).2.1)
    (fun i => (hp i).2.2) hd hd0

 theorem actual_logarithmic_transport_residual {s0 s1 endLog endLog0 : ℝ}
    {a a0 xi : ℝ → I → ℝ} {delta : I → ℝ} {w w0 : ℝ → ℝ}
    (hcomparison : referenceIntegratingFactor s0 s1 (transportReferenceB a0 delta w0) s0*(w s0-w0 s0)+
      (∫ s in s0..s1, referenceIntegratingFactor s0 s1 (transportReferenceB a0 delta w0) s*
        transportLogSource a a0 xi delta w0 s) ≤ w s1-w0 s1) :
    (w0 s1-endLog0)+(endLog0-endLog)+
      referenceIntegratingFactor s0 s1 (transportReferenceB a0 delta w0) s0*(w s0-w0 s0)+
      (∫ s in s0..s1, referenceIntegratingFactor s0 s1 (transportReferenceB a0 delta w0) s*
        transportLogSource a a0 xi delta w0 s) ≤ w s1-endLog := by
  linarith

end OptimalG.Variational
