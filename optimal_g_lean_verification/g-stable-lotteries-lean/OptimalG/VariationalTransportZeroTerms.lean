import OptimalG.VariationalLogTransport

/-! A common four-term RHS can represent the two-term branch by matching
zero coefficients. Positivity is required exactly on the active terms. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter Real

 theorem reciprocal_coefficient_entropy_zero {a a0 delta w w0 xi : ℝ}
    (ha : (a = 0 ∧ a0 = 0) ∨ (0 < a ∧ 0 < a0)) (hxi : 0 < xi) :
    referenceWeight a0 delta w0*(log (a/a0)-delta*(w-w0)-(xi-1)+transportEntropy xi) ≤
      a*exp (-delta*w)/xi-referenceWeight a0 delta w0 := by
  rcases ha with ⟨rfl,rfl⟩ | ha
  · simp [referenceWeight]
  · exact reciprocal_coefficient_entropy ha.1 ha.2 hxi

 theorem logarithmic_field_entropy_zero {I : Type*} [Fintype I]
    {a a0 delta xi : I → ℝ} {w w0 wd w0d : ℝ}
    (ha : ∀ i, (a i = 0 ∧ a0 i = 0) ∨ (0 < a i ∧ 0 < a0 i))
    (hxi : ∀ i, 0 < xi i)
    (hwd : (∑ i, a i*exp (-delta i*w)/xi i) ≤ wd)
    (hw0d : w0d = ∑ i, referenceWeight (a0 i) (delta i) w0) :
    -(∑ i, delta i*referenceWeight (a0 i) (delta i) w0)*(w-w0)+
      (∑ i, referenceWeight (a0 i) (delta i) w0*
        (log (a i/a0 i)-(xi i-1)+transportEntropy (xi i))) ≤ wd-w0d := by
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    reciprocal_coefficient_entropy_zero (delta:=delta i) (w:=w) (w0:=w0) (ha i) (hxi i))
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

 theorem actual_logarithmic_transport_zero {I : Type*} [Fintype I]
    {s0 s1 : ℝ} {a a0 xi : ℝ → I → ℝ} {delta : I → ℝ} {w w0 : ℝ → ℝ}
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
  exact logarithmic_field_entropy_zero (fun i => (hp i).1) (fun i => (hp i).2) hd hd0

end OptimalG.Variational
