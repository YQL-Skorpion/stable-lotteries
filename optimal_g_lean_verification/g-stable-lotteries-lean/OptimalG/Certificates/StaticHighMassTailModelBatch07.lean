import OptimalG.Certificates.ScaledTensorReconstruction5
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper0HighForwardKink
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-20690417652172137151278069042805304949750340226440258206672616094448583539/565096618596266793016980512000000000000000000000000)], [(2188758673898363809783634349709253993398843463650685247998872004578281/22603864743850671720679220480000000000000000000)], [(-17768226637330148792689116774323247085387269913862494963400633652597/289329468721288598024694022144000000000000000)]], [[(186798988495503444275262858708169538426124134979057821628622978360408903/141274154649066698254245128000000000000000000000)], [(-106317882055121891029473364078021607335515768609/26894677387974400000000)], [(1239587439146065379250229551165192175456871361/344251870566072320000)], [(-15295541933292935457516910698836992232895/17212593528303616)]], [[(-9989345948683760086080691729766438407019717031/13447338693987200000000)], [(1018558579579581592231762547161256137404477/537893547759488000)], [(-45886625799878806372550732096510976698685/34425187056607232)]], [[(3498116332725399241815061395769916844657/33618346734968000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[(3498116332725399241815061395769916844657/16809173367484000)]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := flatHigh (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) (kink (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) 0
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

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper0HighForwardKink


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper1HighCapMax
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-3748486330224668047419750275730820634649645106860477961/7063707732453334912712256400000000000000000000000000000000)]], [[(-3749627361259356829044446177511919411344480294058021813188442150109/15231882996669345366073446917469447615000000000000000000000000000000)], [(745658156744762367554288939637959293/1069157557542840310400000000000000000)], [(-3297437173686884379523502527008873/6842608368274177986560000000000000)]], [[(3572148473661177682127797497000020533994578295671356774655841004034176181913/378411717105400374492940241232792068343620535750000000000000000000000000000)], [(-5225940290395326879470059930315437261689/181232981107021044050303250000000000000)], [(219015142949/8141516800)], [(-70963875/10176896)]], [[(-2179491068398648830876733132766922113311/362465962214042088100606500000000000000)], [(390222401/25442240)], [(-212891625/20353792)]], [[(13/20)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := highCapCleared (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000)
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

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper1HighCapMax


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper1HighForwardLeft
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

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper1HighForwardLeft


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper1HighForwardRight
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

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper1HighForwardRight


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper1HighForwardKink
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

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper1HighForwardKink
