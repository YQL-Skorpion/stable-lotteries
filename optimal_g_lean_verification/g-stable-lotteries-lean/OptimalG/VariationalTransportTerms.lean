import OptimalG.Certificates.TransportCoefficients
import OptimalG.VariationalLogDeficit
import OptimalG.VariationalTransportZeroTerms

/-! The actual two/four rational control terms, embedded in one finite
sum compatible with logarithmic transport and the numerical coefficient data. -/
namespace OptimalG.Variational
open Real Certificates.Transport

noncomputable def transportDelta : Fin 4 → ℝ := ![0,0,1,1]
noncomputable def transportXi (xiR xiA : ℝ) : Fin 4 → ℝ := ![xiR,xiA,xiR,xiA]

noncomputable def earlyLogCoefficients (L M S z r a R j mA : ℝ) : Fin 4 → ℝ :=
  ![0,j*earlyNumerator0 L r*mA/earlyDenominator L S r a R,
    0,j*earlyNumerator1 L M S z r R*mA/earlyDenominator L S r a R]

noncomputable def lateLogCoefficients (L M S z r a R j mR mA : ℝ) : Fin 4 → ℝ :=
  ![j*lateNumerator0 L a*mR/lateDenominator L S r a R,
    j*lateNumerator1 L r*mA/lateDenominator L S r a R,
    j*lateNumerator2 L M S z r a*mR/lateDenominator L S r a R,
    j*lateNumerator3 L M z r R*mA/lateDenominator L S r a R]

 theorem early_logarithmic_rhs (L M S z r a R j mA xiR xiA Z : ℝ) (hZ : 0 < Z) :
    (∑ i, earlyLogCoefficients L M S z r a R j mA i*
      exp (-transportDelta i*log Z)/transportXi xiR xiA i) =
      j*earlyAlpha L S r a R (mA/xiA)+j*earlyBeta L M S z r a R (mA/xiA)/Z := by
  simp [earlyLogCoefficients,transportDelta,transportXi,Fin.sum_univ_succ,
    earlyAlpha,earlyBeta,exp_neg,exp_log hZ]
  ring

 theorem late_logarithmic_rhs (L M S z r a R j mR mA xiR xiA Z : ℝ) (hZ : 0 < Z) :
    (∑ i, lateLogCoefficients L M S z r a R j mR mA i*
      exp (-transportDelta i*log Z)/transportXi xiR xiA i) =
      j*lateAlpha L S r a R (mA/xiA) (mR/xiR)+
      j*lateBeta L M S z r a R (mA/xiA) (mR/xiR)/Z := by
  simp [lateLogCoefficients,transportDelta,transportXi,Fin.sum_univ_succ,
    lateAlpha,lateBeta,exp_neg,exp_log hZ]
  ring

 theorem early_tested_log_bound {L M S z r a R j mA xiR xiA Z Yd : ℝ}
    (hZ : 0 < Z) (hj : 0 ≤ j)
    (htest : Yd ≤ Certificates.Control.value (z-L) (h L a) (earlyK L r a) R (P L S r)
      (Certificates.quadratic L (z-r)-S-(M-S-Z)) (mA/xiA) (mA/xiA)) :
    (∑ i, earlyLogCoefficients L M S z r a R j mA i*
      exp (-transportDelta i*log Z)/transportXi xiR xiA i) ≤ -j*Yd/Z := by
  rw [early_logarithmic_rhs _ _ _ _ _ _ _ _ _ _ _ _ hZ]
  apply logDeficit_linear_control hZ hj
  have he := early_transformed_control L M S z r a R (mA/xiA) Z
  linarith

 theorem late_tested_log_bound {L M S z r a R j mR mA xiR xiA Z Yd : ℝ}
    (hZ : 0 < Z) (hj : 0 ≤ j)
    (htest : Yd ≤ Certificates.Control.value (z-L) (h L a) (lateK L r) R (P L S r)
      (Certificates.quadratic L (z-r)-S-(M-S-Z)) (mA/xiA) (mR/xiR)) :
    (∑ i, lateLogCoefficients L M S z r a R j mR mA i*
      exp (-transportDelta i*log Z)/transportXi xiR xiA i) ≤ -j*Yd/Z := by
  rw [late_logarithmic_rhs _ _ _ _ _ _ _ _ _ _ _ _ _ hZ]
  apply logDeficit_linear_control hZ hj
  have he := late_transformed_control L M S z r a R (mA/xiA) (mR/xiR) Z
  linarith

end OptimalG.Variational
