import OptimalG.Certificates.StaticBinaryCentralExpressions
import OptimalG.Certificates.StaticBinaryData.Central.Leaf003

namespace OptimalG.Certificates.StaticBinaryCentralSemantics.Factor
open StaticBinaryCentralExpressions Variational
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem identity (p q u : ℝ) (hpq : p≠q) :
    StaticBinaryData.Central.Leaf003.numerator p q u=-(p-q)*(base p q) := by
  have hpq' : p-q≠0 := sub_ne_zero.mpr hpq
  have hden : (1:ℝ)-(q+1-p)≠0 := by intro he; apply hpq'; linarith only [he]
  norm_num [StaticBinaryData.Central.Leaf003.numerator,StaticBinaryData.Central.Leaf003.numeratorPolynomial,
    RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,
    StaticBinaryCentralExpressions.base,StaticBinaryCentralExpressions.capError,
    StaticBinaryCentralExpressions.rightError,StaticBinaryCentralExpressions.middleError,
    StaticBinaryCentralExpressions.L,StaticBinaryCentralExpressions.S,StaticBinaryCentralExpressions.c,
    StaticBinaryCentralExpressions.initial,StaticBinaryCentralExpressions.slope,
    StaticLow.lam,StaticLow.slack,StaticLow.leftContact,UpperProfileData.leftContact,
    SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,headSlope,
    Variational.quadratic,Variational.capDeficit,Variational.capSlack,Variational.cap,Variational.capScore]
  field_simp
  <;> ring

theorem nonpos {p q : ℝ} (hpq : 0<p-q)
    (hn : 0<StaticBinaryData.Central.Leaf003.numerator p q 0) : base p q≤0 := by
  rw [identity p q 0 (by linarith only [hpq])] at hn
  nlinarith only [hn,hpq]
end OptimalG.Certificates.StaticBinaryCentralSemantics.Factor
