import OptimalG.Certificates.StaticBinaryStationaryExpressions

namespace OptimalG.Certificates.StaticBinaryStationaryModels.CapZero
open StaticBinaryCentralExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
def numeratorPolynomial : RationalPolynomial3 := [[[(2715228910543828409075690082189312500086586907/14572188544837553976138754275765562400000000000)], [(-621368289048966652423125763783953/18215235681046942470173442844706953)], [(-18370791373573889527427706736216047/36430471362093884940346885689413906)], [(6330719887540952059950277500000000/18215235681046942470173442844706953)]], [[(-1/2)], [1], [(-1/2)]], [[(3851596895048060092964100017174000/18215235681046942470173442844706953)], [(-7703193790096120185928200034348000/18215235681046942470173442844706953)], [(3851596895048060092964100017174000/18215235681046942470173442844706953)]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u
def denominatorPolynomial : RationalPolynomial3 := [[[(1/2)], [-1], [(1/2)]]]
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
    819437878441850172740210569189124870439200000000000*numerator p r u=1012915182006552329592044400000000000000000000000000*denominator p r u*
      StaticBinaryStationaryExpressions.CapZero p r := by
  have hrL' : L-r≠0 := sub_ne_zero.mpr hrL.symm
  unfold StaticBinaryStationaryExpressions.CapZero
  unfold Variational.capSlack Variational.capScore
  field_simp [hrL']
  norm_num [numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,
    StaticBinaryStationaryExpressions.CapZero,StaticBinaryStationaryExpressions.headBarrier,
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
end OptimalG.Certificates.StaticBinaryStationaryModels.CapZero
