import OptimalG.Certificates.ScaledTensorReconstruction5
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1CapZeroTriangle
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-68574834745046884706067626951857290116126397/1050573335467750000000000000)], [(259446389841157626147697357404678557073373107/1050573335467750000000000000)], [(-12818596876294189941685666096481523055326327/42022933418710000000000000)], [(1033619051947643302222315006945069833407709/8404586683742000000000000)]], [[(608081628128695810166932936922205779170157/262643333866937500000000)], [(-4941395569262379257939575140825569901342139/525286667733875000000000)], [(17274139311996072872559532697621730473493/1313216669334687500000)], [(-30747853067625138757718302454367226185579/4202293341871000000000)], [1257255231774560595]], [[(-22250599795990608494982888802767118881/2101146670935500000)], [(453464837352495277488707329690240331693/10505733354677500000)], [(-663065951946393619496991407850510633203/10505733354677500000)], [(79001852402988258779427316488421179183/2101146670935500000)], [-7118217872750520000]], [[17116820871853200000], [(-78922350251587985860600823174112097/1050573335467750)], [(62079194762166224678543319444112097/525286667733875)], [(-78993914826382217492138420014112097/1050573335467750)], [15112989114120000000]], [[-9291536700000000000], [54453512316800000000], [-98299494341600000000], [67398419044800000000], [-14260900320000000000]], [[], [-12615800000000000000], [30277920000000000000], [-22708440000000000000], [5046320000000000000]]]
noncomputable def numerator (p u dummy : ℝ) : ℝ := numeratorPolynomial.eval p u dummy
def denominatorPolynomial : RationalPolynomial3 := [[[959396339712000000], [-920317059072000000]], [[], [1302642688000000000]]]
noncomputable def denominator (p u dummy : ℝ) : ℝ := denominatorPolynomial.eval p u dummy
noncomputable def target (p u : ℝ) : ℝ := capCore (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) (p+(527/2000)+u*((97/100)-p-(527/2000))) (8793/100000) (-1757/5000) 0
theorem identity (p u : ℝ) (harg : (1:ℝ)-((p+(527/2000)+u*((97/100)-p-(527/2000)))-p+0)≠0) :
    numerator p u 0= -target p u * denominator p u 0 := by
  have hden : (147300:ℝ)-u*141300+u*p*200000≠0 := by
    intro he
    apply harg
    nlinarith only [he]
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  field_simp [harg,hden]
  <;> ring_nf
  <;> field_simp [hden]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1CapZeroTriangle


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0HeadSquare
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-3748486330224668047419750275730820634649645106860477961/7063707732453334912712256400000000000000000000000000000000)]], [[(-5923048648355923937072301846803874876316751286037044624198543907679209117/70505593879699676986236872315697870277772250000000000000000000000000000000)], [(2096293009122325873347389227381545925482744735474578478763662799294799/8460671265563961238348424677883744433332670000000000000000000000000000)], [(-6727334798802630415283596669242861937796177056950302430822044089121/36098864066406234616953278625637309582219392000000000000000000000000)]], [[(387716622131186393710304217619889899120778187090311808683466171371768049769117061/105095907779965740607549800257342108349005387773311750000000000000000000000000000)], [(-108918545378128011172874967129245092362828926591/10066730921974369508609334263850000000000000000)], [(1279128737326491306774274353111849802826856119/128854155801271929710199478577280000000000000)], [(-3474682092298477128274714468776989105141/1288541558012719297101994785772800000000)]], [[(-14306980093391990385304774909775583892790080279/5033365460987184754304667131925000000000000000)], [(1358262327133038672681363946330928401953883/201334618439487390172186685277000000000000)], [(-3474682092298477128274714468776989105141/859027705341812864734663190515200000000)]], [[(10407573791774069520242584992127229/158267997188523801498756937500000000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := headCleared (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000)
theorem identity (p z : ℝ) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0HeadSquare


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0CapFlat
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-470272463196815730653662341750276712969/2672893893857100776000000000000000000000)], [(47284303827534513663328459687070859/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(65329043794025186891366123589499445919425055330669/10245695027253913855429055761874000000000000000000)], [(-1853030922623433331961472448582379363679806069/100667309219743695086093342638500000000000000)], [(3314077199103694962452914920959907799034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-418545495632493530650371668937675727257693931/100667309219743695086093342638500000000000000)], [(129400413613291329286209694977407893528897/12583413652467961885761667829812500000000)], [(-130366875/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := capCore (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) ((313/1000)-z+p)
theorem identity (p z : ℝ) (harg : (1:ℝ)-(z-p+((313/1000)-z+p))≠0) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  field_simp [harg]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0CapFlat


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0HeadZero
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-489544945756025172411070274336836181369/2672893893857100776000000000000000000000)], [(49747240895804090884722444682158331/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(20767131110825717/3180280000000000)], [(-3664513897785146743365369124120365120400691/191019562086800180429019625500000000000000)], [(3451838563421909209956520099638152845496801/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-675772349176554871232007964386238942099309/191019562086800180429019625500000000000000)], [(118471949899748529291139881557533512721103/12583413652467961885761667829812500000000)], [(-130366875/20353792)]], [[(108293424099618781603825118132872771/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := headLow (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) 0
theorem identity (p z : ℝ) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0HeadZero


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0HeadCapBoundary
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-473320347818799332465137398181697459569/2672893893857100776000000000000000000000)], [(47284303827534513663328459687070859/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(42798588816288963888393249615692967/6682234734642751940000000000000000)], [(-6684359632556589821686560196287265386689/362465962214042088100606500000000000000)], [(3314077199103694962452914920959907799034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-1503722757683952286142384306268672113311/362465962214042088100606500000000000000)], [(129400413613291329286209694977407893528897/12583413652467961885761667829812500000000)], [(-130366875/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := headLow (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) ((527/2000)-z+p)
theorem identity (p z : ℝ) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0HeadCapBoundary
