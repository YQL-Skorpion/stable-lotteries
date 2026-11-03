import OptimalG.Certificates.StaticBinaryStationaryExpressions

namespace OptimalG.Certificates.StaticBinaryStationaryModels.CapShift
open StaticBinaryCentralExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
def numeratorPolynomial : RationalPolynomial3 := [[[(12811/20000)], [1]], [[-1]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p r u : ℝ) : ℝ := denominatorPolynomial.eval p r u
def matchingPolynomial : RationalPolynomial3 := [[[(-319156094422422548078573846306710278291/420229334187100000000000000000000000000)], [(889707746515885023867816193920027/2101146670935500000000000000000000)], [(102929396835454454975939985219/42022933418710000000000000000)], [(-156233/50000)], [1]], [[2], [-4], [2]], [[-1], [2], [-1]]]
noncomputable def matching (p r u : ℝ) : ℝ := matchingPolynomial.eval p r u
theorem matching_eq (p r u : ℝ) (hr1 : r≠1) :
    matching p r u=StaticBinaryStationaryExpressions.capMatch p r := by
  norm_num [matching,matchingPolynomial,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,
    StaticBinaryStationaryExpressions.headMatch,StaticBinaryStationaryExpressions.capMatch,
    StaticBinaryCentralExpressions.L,StaticBinaryCentralExpressions.S,
    StaticBinaryCentralExpressions.initial,StaticBinaryCentralExpressions.slope,
    StaticLow.lam,StaticLow.slack,SmallMassExpressions.initial,SmallMassExpressions.slope,
    headInitial,headSlope,headStationaryLevel,headStationaryConstant,headSlack,
    Variational.quadratic,Variational.cap,Variational.capScore,Variational.capDeficit,
    Variational.capSlack,Variational.stationaryLevel]
  field_simp
  <;> ring

theorem expression_eq (p r u : ℝ) (hr1 : r≠1) (hrL : r≠L)
    (hgap : (1-r)^3-2*L*S≠0) :
    1*numerator p r u=1*denominator p r u*
      StaticBinaryStationaryExpressions.CapShift p r := by
  have hrL' : L-r≠0 := sub_ne_zero.mpr hrL.symm
  norm_num [numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,
    StaticBinaryStationaryExpressions.CapShift,StaticBinaryStationaryExpressions.headBarrier,
    StaticBinaryStationaryExpressions.capBarrier,StaticBinaryCentralExpressions.L,StaticBinaryCentralExpressions.S,
    StaticBinaryCentralExpressions.initial,StaticBinaryCentralExpressions.slope,
    StaticLow.lam,StaticLow.slack,SmallMassExpressions.initial,SmallMassExpressions.slope,
    headInitial,headSlope,headStationaryLevel,headStationaryConstant,headSlack,
    Variational.quadratic,Variational.cap,Variational.capScore,Variational.capDeficit,
    Variational.capSlack,Variational.stationaryLevel,
    Variational.capDiagonalTheta,Variational.capDiagonalAlpha,
    tailSlope,tailCoord,tailOne,tailTwo,Variational.stationaryBarrierCurvature,Variational.capSlopeGap,
    StaticHigh.contact,StaticHigh.contactValue,StaticHigh.contactScore]
  field_simp
  <;> ring
end OptimalG.Certificates.StaticBinaryStationaryModels.CapShift
