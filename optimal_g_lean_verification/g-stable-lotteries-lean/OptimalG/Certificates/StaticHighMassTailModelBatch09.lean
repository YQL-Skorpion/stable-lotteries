import OptimalG.Certificates.ScaledTensorReconstruction5
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighForwardLeft
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-405119042073610645478178104704931354379/2672893893857100776000000000000000000000)], [(88324099790017101331352071059967637/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(4403198873547694503433467762425394222005483/812782596260958971681199000000000000000000)], [(-4239284140313/254422400000)], [(25239628861/1628303360)], [(-39424375/10176896)]], [[(-192037585391/63605600000)], [(40531129/5088448)], [(-118273125/20353792)]], [[(1/2)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := flatHigh (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) (1459/5000) (Variational.capDeficit (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000))
theorem identity (p z : ℝ) (hs : Variational.capSlack (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000)≠0) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,highCapCleared,flatHigh,
    base,splitLinear,flat,massCap,massLower,kink,Variational.capDeficit,Variational.cap,
    Variational.quadratic,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  field_simp [hs]
  norm_num [Variational.capSlack,Variational.capScore]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighForwardLeft


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighForwardRight
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-124307706542923656747387275419809923/855326046034272248320000000000000000)], [(88324099790017101331352071059967637/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(2416994523042161322636263028986190280411/459069526269957058278000000000000000000)], [(-4170455248441/254422400000)], [(25239628861/1628303360)], [(-39424375/10176896)]], [[(-64205183/20353792)], [(40531129/5088448)], [(-118273125/20353792)]], [[(1/2)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := flatHigh (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) (StaticLow.lam:ℝ) 0
theorem identity (p z : ℝ) (hs : Variational.capSlack (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000)≠0) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,highCapCleared,flatHigh,
    base,splitLinear,flat,massCap,massLower,kink,Variational.capDeficit,Variational.cap,
    Variational.quadratic,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  field_simp [hs]
  norm_num [Variational.capSlack,Variational.capScore]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighForwardRight


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighForwardKink
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-17766391642285413927111194132096021186824473887119982126559315794964677289/565096618596266793016980512000000000000000000000000)], [(3886047468131445379000312578196296956674433855682441649743116247721287/45207729487701343441358440960000000000000000000)], [(-16119920724534344743834037552784249779216493821233331700389025732747/289329468721288598024694022144000000000000000)]], [[(158911162886009819409190778899958644331684872993101124196662040860408903/141274154649066698254245128000000000000000000000)], [(-186279164459333287183623051027704234952990566643/53789354775948800000000)], [(1110482824790162696258982751571073446463517311/344251870566072320000)], [(-13876619678266407912161964215966555438145/17212593528303616)]], [[(-8479080573489899829993520567061217243607685781/13447338693987200000000)], [(1783271967734917406599525168536991132228179/1075787095518976000)], [(-41629859034799223736485892647899666314435/34425187056607232)]], [[(3498116332725399241815061395769916844657/33618346734968000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[(3498116332725399241815061395769916844657/16809173367484000)]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := flatHigh (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) (kink (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) 0
theorem identity (p z : ℝ) (hs : Variational.capSlack (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000)≠0) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,highCapCleared,flatHigh,
    base,splitLinear,flat,massCap,massLower,kink,Variational.capDeficit,Variational.cap,
    Variational.quadratic,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  field_simp [hs]
  norm_num [Variational.capSlack,Variational.capScore]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighForwardKink


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighCapMax
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-36669169118411391045002786505191449837422018324567700532828675161/528402076731425941265757795165536400000000000000000000000000000000)]], [[(-42242454576356207684825680169252282622441404626429881801085314189160813789/14066963816967070501821515770668301730852415000000000000000000000000000000)], [(41846706260670808950344743062278771190091/4623571857594012922324800000000000000000)], [(-39942732574815753314702066481326342103/6575746641911485045084160000000000000)]], [[(6488674005484913483571998291689192004391207202168044323424925254943246421696475673/349471167392896459252094664523549363748768780796375750000000000000000000000000000)], [(-1048803767555663421957004441296851958928681/19351654982649691481371269250000000000000)], [(346771025294939/7823997644800)], [(-78220125/10176896)]], [[(-4043844465283093820894812770950052416472118831/334744927889874363244760215486500000000000000)], [(3398072476087/110024966880)], [(-402807570375/19559994112)]], [[(1329399613/1496104020)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := highCapCleared (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000)
theorem identity (p z : ℝ) (hs : Variational.capSlack (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000)≠0) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,highCapCleared,flatHigh,
    base,splitLinear,flat,massCap,massLower,kink,Variational.capDeficit,Variational.cap,
    Variational.quadratic,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  field_simp [hs]
  norm_num [Variational.capSlack,Variational.capScore]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighCapMax


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighForwardLeft
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-15547289469855765011444288323214691469830907/7705953095990021537208000000000000000000000)], [(4920299823205495496593897496055987404819/924714371518802584464960000000000000000)], [(-13314244191605251104900688827108780701/3945447985146891027050496000000000000)]], [[(8650342982576524150725048479104779816097269163/781084075006781571785632239000000000000000000)], [(-34586695074649531/1100249668800000)], [(118198340979913/4694398586880)], [(-43455625/10176896)]], [[(-1204700531743903/183374944800000)], [(374950125023/22004993376)], [(-671345950625/58679982336)]], [[(1/2)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := flatHigh (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) (1459/5000) (Variational.capDeficit (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000))
theorem identity (p z : ℝ) (hs : Variational.capSlack (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000)≠0) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,highCapCleared,flatHigh,
    base,splitLinear,flat,massCap,massLower,kink,Variational.capDeficit,Variational.cap,
    Variational.quadratic,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  field_simp [hs]
  norm_num [Variational.capSlack,Variational.capScore]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighForwardLeft
