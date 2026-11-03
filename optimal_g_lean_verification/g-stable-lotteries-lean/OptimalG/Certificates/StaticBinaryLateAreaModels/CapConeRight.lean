import OptimalG.Certificates.StaticBinaryLateExpressions
import OptimalG.Certificates.PolynomialArithmeticHigher

namespace OptimalG.Certificates.StaticBinaryLateAreaModels.CapConeRight
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
def numeratorPolynomial : RationalPolynomial3 := [[[(379317598926178813385716193920027/8404586683742000000000000000000000)], [(-3230583569399304825309617672020027/8404586683742000000000000000000000)], [(94166349272784454419239014781/84045866837420000000000000000)], [(-256233/200000)], [(1/2)]], [[(-379317598926178813385716193920027/4202293341871000000000000000000000)], [(6081849539872430837233519150120027/8404586683742000000000000000000000)], [(-159820038840837648719239014781/84045866837420000000000000000)], [(356233/200000)], [(-1/2)]], [[(-3062576483393401596466614141564042470589113883875903331/4648738163543463087816841174984274000000000000000000000)], [(149204705231557546781728362951979666675112100799093/46487381635434630878168411749842740000000000000000)], [(-4886634089808996905127285078242372902677/1162184540885865771954210293746068500000)], [(19071056771801434261501387714472269/11621845408858657719542102937460685)]], [[(75699510035314322301154030447192363725309810403/31978476904381695527373906043808058998629000000)], [(-320373827578967024390610178270197584406944410403/31978476904381695527373906043808058998629000000)], [(1838474396695580362454595679975469753408173/159892384521908477636869530219040294993145)], [(-123020561795463370401462988172088730000000/31978476904381695527373906043808058998629)]], [[(-106377828124504138628335458233813252083171/63956953808763391054747812087616117997258)], [(352418951715430879431261434577990712083171/63956953808763391054747812087616117997258)], [(-123020561795463370401462988172088730000000/31978476904381695527373906043808058998629)]]]
noncomputable def numerator (d q u : ℝ) : ℝ := numeratorPolynomial.eval d q u
theorem identity (d q u : ℝ) (hd : 1-d≠0) (hq : 1-q≠0) (hqd : 1-q-d≠0) :
    numerator d q u=(1-d)*(1-q)*(1-q-d)*(areaCap q-upperRight (q+d)-d^2*((B-C*d)/(1-d)*(L-q)-1/2)) := by
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
    0≤areaCap q-upperRight (q+d)-d^2*((B-C*d)/(1-d)*(L-q)-1/2) := by
  have hd1 : 0<1-d := by linarith only [hd.2]
  have hq1 : 0<1-q := by linarith only [hq.2]
  have hqd : 0<1-q-d := by linarith only [hd.2,hq.2]
  rw [identity d q 0 hd1.ne' hq1.ne' hqd.ne'] at hn
  have hD := mul_pos (mul_pos hd1 hq1) hqd
  nlinarith only [hn,hD]
end OptimalG.Certificates.StaticBinaryLateAreaModels.CapConeRight
