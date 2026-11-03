import OptimalG.Certificates.ScaledTensorReconstruction5
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1HeadSquare
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-3748486330224668047419750275730820634649645106860477961/7063707732453334912712256400000000000000000000000000000000)]], [[(-94430698679949000156747878203608615883999309119064519436094733697077017/1382462625092150529141899457170546476034750000000000000000000000000000000)], [(3634350946475149147106993601347777046759136892391990974524714401487873/16921342531127922476696849355767488866665340000000000000000000000000000)], [(-6103259816388429633184340265201146114200478254762302449824155663071/36098864066406234616953278625637309582219392000000000000000000000000)]], [[(324760809709522800054446278115335587941975993111220520911388677457736799769117061/105095907779965740607549800257342108349005387773311750000000000000000000000000000)], [(-187900000190814772625522543303650349567681682757/20133461843948739017218668527700000000000000000)], [(1132485521449609129317700857148503163727356169/128854155801271929710199478577280000000000000)], [(-3152346095875039749952404233859018478091/1288541558012719297101994785772800000000)]], [[(-12591548212426009587545730128321508961958361529/5033365460987184754304667131925000000000000000)], [(2428195105465312610453421387527732078011541/402669236878974780344373370554000000000000)], [(-3152346095875039749952404233859018478091/859027705341812864734663190515200000000)]], [[(10407573791774069520242584992127229/158267997188523801498756937500000000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := headCleared (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000)
theorem identity (p z : ℝ) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1HeadSquare


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1CapFlat
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-403813685427427769550839292657534994219/2672893893857100776000000000000000000000)], [(83398225653477946888564101069792693/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(55610404367714153863782983065732392317862555330669/10245695027253913855429055761874000000000000000000)], [(-1616006218229522667146268806555914508211056069/100667309219743695086093342638500000000000000)], [(2951253188005627461078870205013762779503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-364218274541313486306844457486796821007693931/100667309219743695086093342638500000000000000)], [(115132739137055113882426638417569026341397/12583413652467961885761667829812500000000)], [(-118273125/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := capCore (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) ((313/1000)-z+p)
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

end OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1CapFlat


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1HeadZero
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-423086167986637211308247225244094462619/2672893893857100776000000000000000000000)], [(88324099790017101331352071059967637/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(17750450005981967/3180280000000000)], [(-3214751650358371288308056710407908089150691/191019562086800180429019625500000000000000)], [(3089014552323841708582475383692007825965551/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-572684643121184768113360504327645192099309/191019562086800180429019625500000000000000)], [(104204275423512313887356824997694645533603/12583413652467961885761667829812500000000)], [(-118273125/20353792)]], [[(108293424099618781603825118132872771/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := headLow (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) 0
theorem identity (p z : ℝ) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1HeadZero


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1HeadCapBoundary
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-406861570049411371362314349088955740819/2672893893857100776000000000000000000000)], [(83398225653477946888564101069792693/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(36460099355572492531999421490692967/6682234734642751940000000000000000)], [(-5830920832885289147953519563056796636689/362465962214042088100606500000000000000)], [(2951253188005627461078870205013762779503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-1308110412227842033545330302362422113311/362465962214042088100606500000000000000)], [(115132739137055113882426638417569026341397/12583413652467961885761667829812500000000)], [(-118273125/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := headLow (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) ((527/2000)-z+p)
theorem identity (p z : ℝ) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1HeadCapBoundary


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0HeadSquare
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-36669169118411391045002786505191449837422018324567700532828675161/528402076731425941265757795165536400000000000000000000000000000000)]], [[(-37576735389196839995752664856952036019104416905668973234066042002727498030929/59013182077308629637480262128239117422495373250000000000000000000000000000000)], [(207335923288189010766721494947054875985595437157033017999644407551100716551/73176345775862700750475525039016505603894262830000000000000000000000000000)], [(-665373669476905753265835399413092350924223702678054151905731859326807529/312219075310347523202028906833137090576615521408000000000000000000000000)]], [[(564227632913903249902971199142281933232570839337400966273038644233626863828121495621/100997167376547076723855358047305766123394177650152591750000000000000000000000000000)], [(-1517794107871986596714203503173888119055463611125559/87067155744156321879962132048038650000000000000000)], [(5535425099112912635161595125938314708099604351077/371486531175066973354505096738298240000000000000)], [(-3474682092298477128274714468776989105141/1288541558012719297101994785772800000000)]], [[(-6189421775127653782134559034229230334573105836641/1404308963615424546451002129807075000000000000000)], [(19110240137150600688205361176842380249897551267/1741343114883126437599242640960773000000000000)], [(-53680363643919173154716063828135704685323309/7429730623501339467090101934765964800000000)]], [[(416589928088877360721174205096908403621/1368859907683542359162748752437500000000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := headCleared (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000)
theorem identity (p z : ℝ) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0HeadSquare
