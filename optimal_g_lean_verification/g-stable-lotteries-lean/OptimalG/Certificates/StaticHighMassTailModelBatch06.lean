import OptimalG.Certificates.ScaledTensorReconstruction5
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower1HeadZero
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-41845753856088179945634469864464173007191731/23117859287970064611624000000000000000000000)], [(8735782020390606888986639406597660092413/1849428743037605168929920000000000000000)], [(-12079121076993306885558983309485175651/3945447985146891027050496000000000000)]], [[(269726424526310272583/27506241720000000000)], [(-54979354458733880472210236049519216921223807/1973868808230268531099869463500000000000000)], [(4527610922282892023757583141586539075965551/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-11249454848706009767675674335832416985026193/1973868808230268531099869463500000000000000)], [(64300321071919019248267922701184673511201/4194471217489320628587222609937500000000)], [(-609067169375/58679982336)]], [[(108293424099618781603825118132872771/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := headLow (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) 0
theorem identity (p z : ℝ) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower1HeadZero


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower1HeadCapBoundary
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-40241044028475493916242999576998378202343531/23117859287970064611624000000000000000000000)], [(2749527863584958928395524175384212333919/616476247679201722976640000000000000000)], [(-12079121076993306885558983309485175651/3945447985146891027050496000000000000)]], [[(564033003827858057076699486993003471583/57794648219925161529060000000000000000)], [(-9229398756510276268445451280610081567858129/348329789687694446664682846500000000000000)], [(4389849557964677776253977962908294029503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-2376064257466791630445175533628537650891871/348329789687694446664682846500000000000000)], [(198882773394973222243100582260928401341397/12583413652467961885761667829812500000000)], [(-609067169375/58679982336)]], [[(174407730781350603221506819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := headLow (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) ((527/2000)-z+p)
theorem identity (p z : ℝ) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower1HeadCapBoundary


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper0HighCapMax
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

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper0HighCapMax


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper0HighForwardLeft
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

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper0HighForwardLeft


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper0HighForwardRight
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

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper0HighForwardRight
