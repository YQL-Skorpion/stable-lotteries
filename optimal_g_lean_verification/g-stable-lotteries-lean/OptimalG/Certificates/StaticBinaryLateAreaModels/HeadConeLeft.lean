import OptimalG.Certificates.StaticBinaryLateExpressions
import OptimalG.Certificates.PolynomialArithmeticHigher

namespace OptimalG.Certificates.StaticBinaryLateAreaModels.HeadConeLeft
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
def numeratorPolynomial : RationalPolynomial3 := [[[(351624010926115571431568191/84045866837420000000000000000)], [(-11978055991292783365235876987410393/475752523158618900930000000000000000)], [(231747054311016597457026722502434981239/5627306566703068497733580000000000000000)], [(-9947174049994340395071814975520750683/422047992502730137330018500000000000000)], [(1069761957651165231815925679627229/316535994377047602997513875000000000)]], [[(4184296501231770880558431809/42022933418710000000000000000)], [(-46004791982556428209026628599037557181/96102009678041017987860000000000000000)], [(33657517813091733747521830846511131726889/50645759100327616479602220000000000000000)], [(-357117919069443155192448001854928831951/1266143977508190411990055500000000000000)], [(-1069761957651165231815925679627229/316535994377047602997513875000000000)]], [[(-49747272418392190485355931600191363752244154606823/46487381635434630878168411749842740000000000000000)], [(254013257322471735118539180329926101785513035500835653622049/53155865576083661658286486614941781746001420000000000000000)], [(-4310600631553551852416106133777641316849022100203956278545897/700328528964902242347924461151857974503568708500000000000000)], [(428353619545672721713782931509499950172400747161084124437/175082132241225560586981115287964493625892177125000000000)]], [[(89032589621712918893148323585381773439701157802301/31978476904381695527373906043808058998629000000000)], [(-348528931210546536859542276859692029467200299302301/31978476904381695527373906043808058998629000000000)], [(765033806768593976735713882892797972054998283/63956953808763391054747812087616117997258000)], [(-123020561795463370401462988172088730000000/31978476904381695527373906043808058998629)]], [[(-116259177487958082546293995201349942313747361/63956953808763391054747812087616117997258000)], [(362300301078884823349219971545527402313747361/63956953808763391054747812087616117997258000)], [(-123020561795463370401462988172088730000000/31978476904381695527373906043808058998629)]]]
noncomputable def numerator (d q u : ℝ) : ℝ := numeratorPolynomial.eval d q u
theorem identity (d q u : ℝ) (hd : 1-d≠0) (hq : 1-q≠0) (hqd : 1-q-d≠0) :
    numerator d q u=(1-d)*(1-q)*(1-q-d)*(areaHead q-upperLeft (q+d)-d^2*((B-C*d)/(1-d)*(L-q)-1/2)) := by
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
    0≤areaHead q-upperLeft (q+d)-d^2*((B-C*d)/(1-d)*(L-q)-1/2) := by
  have hd1 : 0<1-d := by linarith only [hd.2]
  have hq1 : 0<1-q := by linarith only [hq.2]
  have hqd : 0<1-q-d := by linarith only [hd.2,hq.2]
  rw [identity d q 0 hd1.ne' hq1.ne' hqd.ne'] at hn
  have hD := mul_pos (mul_pos hd1 hq1) hqd
  nlinarith only [hn,hD]
end OptimalG.Certificates.StaticBinaryLateAreaModels.HeadConeLeft
