import OptimalG.Certificates.StaticBinaryStationaryExpressions

namespace OptimalG.Certificates.StaticBinaryStationaryModels.HeadLate
open StaticBinaryCentralExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
def numeratorPolynomial : RationalPolynomial3 := [[[(-16963821056204441531225967048789798069369706627199645633429145207592139255479861/272828107146611912731912101074854266466676166130816445775000000000000000000000000)], [(9522989181870098020792502302525200383358280295412295051839099369971612376098466017/39633352618703188195688500714334223246069885529255019754436068750000000000000000000)], [(-17140742787877949642200067625730784910898980858834180763085855474133214933067/74312536160068477866915938839376668586381035367353162039567628906250000000000)]], [[(30735084661821259425447631781955152107631760750061390733354241904066914779678113/173875353423988180471407616037079172950500142967054280213009850000000000000000000)], [(1602465100356422722335868957527755979818101636184481378046532194133120654163957/2545341979290049197456439268098353448469821537323266824229338637500000000000000)], [(49974573088905019894931819367127229/79133998594261900749378468750000000)]], [[(-182544077656755610936003800014187686762235221/1085567434062004470655488293360878941943500000)], [-1]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u
def denominatorPolynomial : RationalPolynomial3 := [[[(56233/100000)], [-1]]]
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
    137448466881662656662647720477311086217370363015456408508384286425000000000000000000000000*numerator p r u=100404104837054215738937478932176155585752807506301611251509136169846800000000000000000000*denominator p r u*
      StaticBinaryStationaryExpressions.HeadLate p r := by
  have hrL' : L-r≠0 := sub_ne_zero.mpr hrL.symm
  unfold StaticBinaryStationaryExpressions.HeadLate
  field_simp [hrL']
  norm_num [numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,
    StaticBinaryStationaryExpressions.HeadLate,StaticBinaryStationaryExpressions.headBarrier,
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
end OptimalG.Certificates.StaticBinaryStationaryModels.HeadLate
