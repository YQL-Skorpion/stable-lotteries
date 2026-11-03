import OptimalG.Certificates.StaticBinaryStationaryExpressions

namespace OptimalG.Certificates.StaticBinaryStationaryModels.HeadZero
open StaticBinaryCentralExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
def numeratorPolynomial : RationalPolynomial3 := [[[(893254233839719765329862014612471379951/1821523568104694247017344284470695300000)], [(99949146177810039789863638734254458/455380892026173561754336071117673825)]], [[-1]], [[(7703193790096120185928200034348000/18215235681046942470173442844706953)]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p r u : ℝ) : ℝ := denominatorPolynomial.eval p r u
def matchingPolynomial : RationalPolynomial3 := [[[(-108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(-2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[2]], [[-1]]]
noncomputable def matching (p r u : ℝ) : ℝ := matchingPolynomial.eval p r u
theorem matching_eq (p r u : ℝ) (hr1 : r≠1) :
    matching p r u=StaticBinaryStationaryExpressions.headMatch p r := by
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
    (1024297348052312715925263211486406088049/1266143977508190411990055500000000000000)*numerator p r u=1*denominator p r u*
      StaticBinaryStationaryExpressions.HeadZero p r := by
  have hrL' : L-r≠0 := sub_ne_zero.mpr hrL.symm
  norm_num [numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,
    StaticBinaryStationaryExpressions.HeadZero,StaticBinaryStationaryExpressions.headBarrier,
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
end OptimalG.Certificates.StaticBinaryStationaryModels.HeadZero
