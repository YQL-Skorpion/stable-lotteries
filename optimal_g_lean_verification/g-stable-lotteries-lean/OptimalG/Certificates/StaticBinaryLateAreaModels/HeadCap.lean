import OptimalG.Certificates.StaticBinaryLateExpressions
import OptimalG.Certificates.PolynomialArithmeticHigher

namespace OptimalG.Certificates.StaticBinaryLateAreaModels.HeadCap
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
def numeratorPolynomial : RationalPolynomial3 := [[[(-185708249545084491605614715820027/8404586683742000000000000000000000)], [(2052376411113010800592125889777736660133941/9610200967804101798786000000000000000000000)], [(-48535717320175218807072122265958177439/70341332083788356221669750000000000000)], [(354797602992559382307707544432352749317/422047992502730137330018500000000000000)], [(-108293424099618781603825118132872771/316535994377047602997513875000000000)]], [[(2843364870637116181749414715820027/8404586683742000000000000000000000)], [(-18906710525453216071058155865767717912133941/9610200967804101798786000000000000000000000)], [(4393145350794828140202415316210314357853/1266143977508190411990055500000000000000)], [(-2763710482884343685328478605828549331951/1266143977508190411990055500000000000000)], [(108293424099618781603825118132872771/316535994377047602997513875000000000)]], [[(-41869083730168324581000800546874726845417593/23243690817717315439084205874921370000000000)], [(10078068656559977269551462849717084966450412504994712492311/1328896639402091541457162165373544543650035500000000000000)], [(-6488938668418447171794734556217892388031601014488974805545897/700328528964902242347924461151857974503568708500000000000000)], [(609826249613703015262188857505475147815637988751146624437/175082132241225560586981115287964493625892177125000000000)]], [[(29167303849629124312870505195951928908072083297/7994619226095423881843476510952014749657250000)], [(-102327812074685435657999756918131256202966608297/7994619226095423881843476510952014749657250000)], [(4156625946956886157819799950608060391795781/319784769043816955273739060438080589986290)], [(-123020561795463370401462988172088730000000/31978476904381695527373906043808058998629)]], [[(-69178152514442917077854682138810655540900/31978476904381695527373906043808058998629)], [(192198714309906287479317670310899385540900/31978476904381695527373906043808058998629)], [(-123020561795463370401462988172088730000000/31978476904381695527373906043808058998629)]]]
noncomputable def numerator (d q u : ℝ) : ℝ := numeratorPolynomial.eval d q u
theorem identity (d q u : ℝ) (hd : 1-d≠0) (hq : 1-q≠0) (hqd : 1-q-d≠0) :
    numerator d q u=(1-d)*(1-q)*(1-q-d)*(areaHead q-areaCap (q+d)-d^2*((B-C*d)/(1-d)*(L-q)-1/2)) := by
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
    0≤areaHead q-areaCap (q+d)-d^2*((B-C*d)/(1-d)*(L-q)-1/2) := by
  have hd1 : 0<1-d := by linarith only [hd.2]
  have hq1 : 0<1-q := by linarith only [hq.2]
  have hqd : 0<1-q-d := by linarith only [hd.2,hq.2]
  rw [identity d q 0 hd1.ne' hq1.ne' hqd.ne'] at hn
  have hD := mul_pos (mul_pos hd1 hq1) hqd
  nlinarith only [hn,hD]
end OptimalG.Certificates.StaticBinaryLateAreaModels.HeadCap
