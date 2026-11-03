import OptimalG.Certificates.StaticBinaryLateExpressions
import OptimalG.Certificates.PolynomialArithmeticHigher

namespace OptimalG.Certificates.StaticBinaryLateAreaModels.CapConeLeft
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
def numeratorPolynomial : RationalPolynomial3 := [[[(220870650637696048748771534920027/8404586683742000000000000000000000)], [(-2006505570390762005637728354020027/8404586683742000000000000000000000)], [(61453111314886690964909568191/84045866837420000000000000000)], [(-864225831/1000000000)], [(691/2000)]], [[(232721400578092596450228465079973/4202293341871000000000000000000000)], [(-619244999995604618269314826879973/8404586683742000000000000000000000)], [(-44037686702401389456949568191/84045866837420000000000000000)], [(900725831/1000000000)], [(-691/2000)]], [[(-4872008445611548575103892712475887428264800664648903331/4648738163543463087816841174984274000000000000000000000)], [(213246145852541618943108723950507355374435088606823/46487381635434630878168411749842740000000000000000)], [(-6573984649479660749803250931628906630491153/1162184540885865771954210293746068500000000)], [(9783112847522968845803660970394118599/4648738163543463087816841174984274000)]], [[(89032589621712918893148323585381773439701157802301/31978476904381695527373906043808058998629000000000)], [(-348528931210546536859542276859692029467200299302301/31978476904381695527373906043808058998629000000000)], [(765033806768593976735713882892797972054998283/63956953808763391054747812087616117997258000)], [(-123020561795463370401462988172088730000000/31978476904381695527373906043808058998629)]], [[(-116259177487958082546293995201349942313747361/63956953808763391054747812087616117997258000)], [(362300301078884823349219971545527402313747361/63956953808763391054747812087616117997258000)], [(-123020561795463370401462988172088730000000/31978476904381695527373906043808058998629)]]]
noncomputable def numerator (d q u : ℝ) : ℝ := numeratorPolynomial.eval d q u
theorem identity (d q u : ℝ) (hd : 1-d≠0) (hq : 1-q≠0) (hqd : 1-q-d≠0) :
    numerator d q u=(1-d)*(1-q)*(1-q-d)*(areaCap q-upperLeft (q+d)-d^2*((B-C*d)/(1-d)*(L-q)-1/2)) := by
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
    0≤areaCap q-upperLeft (q+d)-d^2*((B-C*d)/(1-d)*(L-q)-1/2) := by
  have hd1 : 0<1-d := by linarith only [hd.2]
  have hq1 : 0<1-q := by linarith only [hq.2]
  have hqd : 0<1-q-d := by linarith only [hd.2,hq.2]
  rw [identity d q 0 hd1.ne' hq1.ne' hqd.ne'] at hn
  have hD := mul_pos (mul_pos hd1 hq1) hqd
  nlinarith only [hn,hD]
end OptimalG.Certificates.StaticBinaryLateAreaModels.CapConeLeft
