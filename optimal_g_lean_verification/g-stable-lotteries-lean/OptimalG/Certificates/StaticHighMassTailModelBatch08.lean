import OptimalG.Certificates.ScaledTensorReconstruction5
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper0HighCapMax
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-3748486330224668047419750275730820634649645106860477961/7063707732453334912712256400000000000000000000000000000000)]], [[(-4431332756651440461141449387814368601408005139136345192094692150109/15231882996669345366073446917469447615000000000000000000000000000000)], [(423095797379541045748562152188550259/534578778771420155200000000000000000)], [(-3634609129017190887995840251120023/6842608368274177986560000000000000)]], [[(4218250533328254666013211470484069387332083459447804235593341004034176181913/378411717105400374492940241232792068343620535750000000000000000000000000000)], [(-5994035210099497485829796500222859136689/181232981107021044050303250000000000000)], [(245424351899/8141516800)], [(-78220125/10176896)]], [[(-2531593290219647285551430339798172113311/362465962214042088100606500000000000000)], [(221074063/12721120)], [(-234660375/20353792)]], [[(13/20)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := highCapCleared (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000)
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

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper0HighCapMax


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper0HighForwardLeft
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-471577819842998606581001153797673073129/2672893893857100776000000000000000000000)], [(49747240895804090884722444682158331/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(5174170580594332314690692996593362972005483/812782596260958971681199000000000000000000)], [(-2419165294819/127211200000)], [(28173985411/1628303360)], [(-43455625/10176896)]], [[(-226363679141/63605600000)], [(23150327/2544224)], [(-130366875/20353792)]], [[(1/2)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := flatHigh (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) (1459/5000) (Variational.capDeficit (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000))
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

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper0HighForwardLeft


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper0HighForwardRight
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-145574515429127804300290651129487273/855326046034272248320000000000000000)], [(49747240895804090884722444682158331/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(2852448748993382904820519021173690280411/459069526269957058278000000000000000000)], [(-2384750848883/127211200000)], [(28173985411/1628303360)], [(-43455625/10176896)]], [[(-75189533/20353792)], [(23150327/2544224)], [(-130366875/20353792)]], [[(1/2)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := flatHigh (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) (StaticLow.lam:ℝ) 0
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

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper0HighForwardRight


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper0HighForwardKink
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

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper0HighForwardKink


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighCapMax
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

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighCapMax
