import OptimalG.VariationalTransportTerms

/-! Exact reference sums and adjoint weights for the two/four-term logarithmic
control representation. These connect the affine reference ODE to the same
four coefficients differentiated by the numerical certificates. -/
namespace OptimalG.Variational
open Real Certificates.Transport

theorem early_reference_sum (L M S z r a R mA Z : ℝ) (hZ : 0<Z) :
    (∑ i,referenceWeight (earlyLogCoefficients L M S z r a R 1 mA i)
      (transportDelta i) (log Z))=
      earlyAlpha L S r a R mA+earlyBeta L M S z r a R mA/Z := by
  simp [earlyLogCoefficients,transportDelta,referenceWeight,Fin.sum_univ_succ,
    earlyAlpha,earlyBeta,exp_neg,exp_log hZ]
  ring

theorem late_reference_sum (L M S z r a R mR mA Z : ℝ) (hZ : 0<Z) :
    (∑ i,referenceWeight (lateLogCoefficients L M S z r a R 1 mR mA i)
      (transportDelta i) (log Z))=
      lateAlpha L S r a R mA mR+lateBeta L M S z r a R mA mR/Z := by
  simp [lateLogCoefficients,transportDelta,referenceWeight,Fin.sum_univ_succ,
    lateAlpha,lateBeta,exp_neg,exp_log hZ]
  ring

theorem early_reference_B (L M S z r a R mA Z : ℝ) (hZ : 0<Z) :
    (∑ i,transportDelta i*referenceWeight
      (earlyLogCoefficients L M S z r a R 1 mA i) (transportDelta i) (log Z))=
      earlyBeta L M S z r a R mA/Z := by
  simp [earlyLogCoefficients,transportDelta,referenceWeight,Fin.sum_univ_succ,
    earlyBeta,exp_neg,exp_log hZ]
  ring

theorem late_reference_B (L M S z r a R mR mA Z : ℝ) (hZ : 0<Z) :
    (∑ i,transportDelta i*referenceWeight
      (lateLogCoefficients L M S z r a R 1 mR mA i) (transportDelta i) (log Z))=
      lateBeta L M S z r a R mA mR/Z := by
  simp [lateLogCoefficients,transportDelta,referenceWeight,Fin.sum_univ_succ,
    lateBeta,exp_neg,exp_log hZ]
  ring

theorem reference_weight_power {E Z terminal coefficient : ℝ}
    (hZ : 0<Z) (i : Fin 4) :
    (E*Z/terminal)*referenceWeight coefficient (transportDelta i) (log Z)=
      (E/terminal)*(if i.val<2 then Z else 1)*coefficient := by
  fin_cases i <;>
    simp [transportDelta,referenceWeight,exp_neg,exp_log hZ] <;>
    field_simp [hZ.ne'] <;> ring <;> simp

end OptimalG.Variational
