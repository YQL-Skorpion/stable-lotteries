import OptimalG.Certificates.StaticBinaryLateExpressions
import OptimalG.Certificates.PolynomialArithmeticHigher

namespace OptimalG.Certificates.StaticBinaryLateAreaModels.HeadConeRight
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
def numeratorPolynomial : RationalPolynomial3 := [[[(1936093493810943217801014781/84045866837420000000000000000)], [(-81268577760530163567646709905969363/475752523158618900930000000000000000)], [(2422067955334032220564884279145647014149/5627306566703068497733580000000000000000)], [(-185915513322200874084705607120147250683/422047992502730137330018500000000000000)], [(49974573088905019894931819367127229/316535994377047602997513875000000000)]], [[(-1936093493810943217801014781/42022933418710000000000000000)], [(30618684763731435124361744996135810729/96102009678041017987860000000000000000)], [(-36112541502445591692059540267988136569301/50645759100327616479602220000000000000000)], [(757644832322222701833844098828950668049/1266143977508190411990055500000000000000)], [(-49974573088905019894931819367127229/316535994377047602997513875000000000)]], [[(-31652952796210720698983145891072914175487286799093/46487381635434630878168411749842740000000000000000)], [(180785252449145727117740085154636548994771231084943439497459/53155865576083661658286486614941781746001420000000000000000)], [(-3293808810866004724463528349370936195214734388638169805545897/700328528964902242347924461151857974503568708500000000000000)], [(347203051251864674381717184573528407376799723063646624437/175082132241225560586981115287964493625892177125000000000)]], [[(75699510035314322301154030447192363725309810403/31978476904381695527373906043808058998629000000)], [(-320373827578967024390610178270197584406944410403/31978476904381695527373906043808058998629000000)], [(1838474396695580362454595679975469753408173/159892384521908477636869530219040294993145)], [(-123020561795463370401462988172088730000000/31978476904381695527373906043808058998629)]], [[(-106377828124504138628335458233813252083171/63956953808763391054747812087616117997258)], [(352418951715430879431261434577990712083171/63956953808763391054747812087616117997258)], [(-123020561795463370401462988172088730000000/31978476904381695527373906043808058998629)]]]
noncomputable def numerator (d q u : ℝ) : ℝ := numeratorPolynomial.eval d q u
theorem identity (d q u : ℝ) (hd : 1-d≠0) (hq : 1-q≠0) (hqd : 1-q-d≠0) :
    numerator d q u=(1-d)*(1-q)*(1-q-d)*(areaHead q-upperRight (q+d)-d^2*((B-C*d)/(1-d)*(L-q)-1/2)) := by
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
    0≤areaHead q-upperRight (q+d)-d^2*((B-C*d)/(1-d)*(L-q)-1/2) := by
  have hd1 : 0<1-d := by linarith only [hd.2]
  have hq1 : 0<1-q := by linarith only [hq.2]
  have hqd : 0<1-q-d := by linarith only [hd.2,hq.2]
  rw [identity d q 0 hd1.ne' hq1.ne' hqd.ne'] at hn
  have hD := mul_pos (mul_pos hd1 hq1) hqd
  nlinarith only [hn,hD]
end OptimalG.Certificates.StaticBinaryLateAreaModels.HeadConeRight
