import OptimalG.Certificates.StaticBinaryLateExpressions
import OptimalG.Certificates.PolynomialArithmeticHigher

namespace OptimalG.Certificates.StaticBinaryLateAreaModels.HeadHead
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
def numeratorPolynomial : RationalPolynomial3 := [[], [[(299715285114539778168239594731354687/2402550241951025449696500000000000000)], [(-357848247610982542674389543891932836049/633071988754095205995027750000000000000)], [(957543124677842781413571376297459584049/1266143977508190411990055500000000000000)], [(-49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[(-43237769662516029057381981259653205743073321161729188147567/38907140498050124574884692286214331916864928250000000000000)], [(378982740863337479211260657172728851202409168847392065568701/77814280996100249149769384572428663833729856500000000000000)], [(-4353079762414248667705191458700883715126864705656230207966103/700328528964902242347924461151857974503568708500000000000000)], [(215064368571187484729590150852510219710062745867603375563/87541066120612780293490557643982246812946088562500000000)]], [[(9017485955874093204245948856903056479797647113617627386926246155817/3211687258077073654445543286265662136336071498446731500000000000000)], [(-11703995624183318737674517232956067779621141796981767710529525079939/1070562419359024551481847762088554045445357166148910500000000000000)], [(9612449409111661872418594633011298905015468733081918936165582271/802921814519268413611385821566415534084017874611682875000000000)], [(-123020561795463370401462988172088730000000/31978476904381695527373906043808058998629)]], [[(-4386727682759196883213682885021193884706646571868596348665582271/2408765443557805240834157464699246602252053623835048625000000000)], [(13653200222587285243886264652581230455453719063118596348665582271/2408765443557805240834157464699246602252053623835048625000000000)], [(-123020561795463370401462988172088730000000/31978476904381695527373906043808058998629)]]]
noncomputable def numerator (d q u : ℝ) : ℝ := numeratorPolynomial.eval d q u
theorem identity (d q u : ℝ) (hd : 1-d≠0) (hq : 1-q≠0) (hqd : 1-q-d≠0) :
    numerator d q u=(1-d)*(1-q)*(1-q-d)*(areaHead q-areaHead (q+d)-d^2*((B-C*d)/(1-d)*(L-q)-1/2)) := by
  have hqd' : (1:ℝ)-(q+d)≠0 := by intro he; apply hqd; linarith only [he]
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,StaticBinaryLateExpressions.areaHead,StaticBinaryLateExpressions.areaCap,
    StaticBinaryLateExpressions.areaLinear,StaticBinaryLateExpressions.areaQuadratic,
    StaticBinaryLateExpressions.upperLeft,StaticBinaryLateExpressions.upperRight,
    StaticBinaryLateExpressions.cutoff,binaryAreaCutoff,
    StaticBinaryCentralExpressions.L,StaticBinaryCentralExpressions.S,StaticBinaryCentralExpressions.c,
    StaticBinaryCentralExpressions.initial,StaticBinaryCentralExpressions.slope,
    StaticLow.lam,StaticLow.slack,StaticLow.leftContact,UpperProfileData.leftContact,
    SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,headSlope,
    Variational.cap,Variational.capScore,Variational.capSlack,Variational.capDeficit,Variational.quadratic,
    StaticBinaryLateScalars.B,StaticBinaryLateScalars.C,StaticHigh.tailSlope,StaticHigh.tailCurvature]
  field_simp
  <;> ring

theorem nonneg {d q : ℝ} (hd : d∈Icc (1/50:ℝ) (7/80))
    (hq : q∈Icc (0:ℝ) (337/1000)) (hn : 0<numerator d q 0) :
    0≤areaHead q-areaHead (q+d)-d^2*((B-C*d)/(1-d)*(L-q)-1/2) := by
  have hd1 : 0<1-d := by linarith only [hd.2]
  have hq1 : 0<1-q := by linarith only [hq.2]
  have hqd : 0<1-q-d := by linarith only [hd.2,hq.2]
  rw [identity d q 0 hd1.ne' hq1.ne' hqd.ne'] at hn
  have hD := mul_pos (mul_pos hd1 hq1) hqd
  nlinarith only [hn,hD]
end OptimalG.Certificates.StaticBinaryLateAreaModels.HeadHead
