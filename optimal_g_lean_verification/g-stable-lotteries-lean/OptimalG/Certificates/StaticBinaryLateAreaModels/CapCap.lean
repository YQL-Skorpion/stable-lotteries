import OptimalG.Certificates.StaticBinaryLateExpressions
import OptimalG.Certificates.PolynomialArithmeticHigher

namespace OptimalG.Certificates.StaticBinaryLateAreaModels.CapCap
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
def numeratorPolynomial : RationalPolynomial3 := [[], [[(2471948371546947198538185284179973/8404586683742000000000000000000000)], [(-156233/100000)], [(456233/200000)], [-1]], [[(-8271097949805994442768459661831696422123903803966603331/4648738163543463087816841174984274000000000000000000000)], [(17182481164966200421094414525427606208733/2324369081771731543908420587492137000000)], [(-5094451743114404446243568663854436801141/581092270442932885977105146873034250000)], [(73007649770178841681629084241326593/23243690817717315439084205874921370)]], [[(29167303849629124312870505195951928908072083297/7994619226095423881843476510952014749657250000)], [(-102327812074685435657999756918131256202966608297/7994619226095423881843476510952014749657250000)], [(4156625946956886157819799950608060391795781/319784769043816955273739060438080589986290)], [(-123020561795463370401462988172088730000000/31978476904381695527373906043808058998629)]], [[(-69178152514442917077854682138810655540900/31978476904381695527373906043808058998629)], [(192198714309906287479317670310899385540900/31978476904381695527373906043808058998629)], [(-123020561795463370401462988172088730000000/31978476904381695527373906043808058998629)]]]
noncomputable def numerator (d q u : ℝ) : ℝ := numeratorPolynomial.eval d q u
theorem identity (d q u : ℝ) (hd : 1-d≠0) (hq : 1-q≠0) (hqd : 1-q-d≠0) :
    numerator d q u=(1-d)*(1-q)*(1-q-d)*(areaCap q-areaCap (q+d)-d^2*((B-C*d)/(1-d)*(L-q)-1/2)) := by
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
    0≤areaCap q-areaCap (q+d)-d^2*((B-C*d)/(1-d)*(L-q)-1/2) := by
  have hd1 : 0<1-d := by linarith only [hd.2]
  have hq1 : 0<1-q := by linarith only [hq.2]
  have hqd : 0<1-q-d := by linarith only [hd.2,hq.2]
  rw [identity d q 0 hd1.ne' hq1.ne' hqd.ne'] at hn
  have hD := mul_pos (mul_pos hd1 hq1) hqd
  nlinarith only [hn,hD]
end OptimalG.Certificates.StaticBinaryLateAreaModels.CapCap
