import OptimalG.Certificates.ScaledTensorReconstruction5
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadCapBoundaryRectangle
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

end OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadCapBoundaryRectangle


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0CapZeroRectangle
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-81677420612452142312958852841103555802630147/1050573335467750000000000000)], [(20944927441142773987972480192613695355371611/1050573335467750000000000000)], [(-70701503796973229766801628802337758746233/42022933418710000000000000)], [(391850844808472366825719533313500799653/8404586683742000000000000)]], [[(729995935348161524179679085143745301873907/262643333866937500000000)], [(-3882043341363562997194145795750389990953/5252866677338750000000)], [(144465546148494981356736620971699705047/2101146670935500000000)], [(-26182914145832169/10)], [33394639989645]], [[(-25872795784469181685099363796613310431/2101146670935500000)], [(5089454774157955961495329556502320253/2101146670935500000)], [-152344835896235400], [3035876362695000]], [[19332719318713200000], [-2516052392211600000], [81774447480000000]], [[-10241621700000000000], [688337100000000000]]]
noncomputable def numerator (p u dummy : ℝ) : ℝ := numeratorPolynomial.eval p u dummy
def denominatorPolynomial : RationalPolynomial3 := [[[959396339712000000], [-64480813056000000]]]
noncomputable def denominator (p u dummy : ℝ) : ℝ := denominatorPolynomial.eval p u dummy
noncomputable def target (p u : ℝ) : ℝ := capCore (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) (p+(527/2000)+u*((313/1000)-(527/2000))) (8793/100000) (-3589/10000) 0
theorem identity (p u : ℝ) (harg : (1:ℝ)-((p+(527/2000)+u*((313/1000)-(527/2000)))-p+0)≠0) :
    numerator p u 0= -target p u * denominator p u 0 := by
  have hden : (1473:ℝ)-u*99≠0 := by
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

end OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0CapZeroRectangle


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0CapZeroTriangle
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-81677420612452142312958852841103555802630147/1050573335467750000000000000)], [(298941237114492319646516308203668197344849357/1050573335467750000000000000)], [(-14402655926376802814230523540072920787899977/42022933418710000000000000)], [(1139309422515697635666629783571137152570659/8404586683742000000000000)]], [[(729995935348161524179679085143745301873907/262643333866937500000000)], [(-5752299510866810358500053344769129303808389/525286667733875000000000)], [(19667360217144877510237247404371120231843/1313216669334687500000)], [(-34409726862768934008450846481015851067029/4202293341871000000000)], [1385813012413852845]], [[(-25872795784469181685099363796613310431/2101146670935500000)], [(520052235806870816734758449491822753043/10505733354677500000)], [(-749800529542616319510651538273143855053/10505733354677500000)], [(88179417001922971638318221966477530833/2101146670935500000)], [-7846075087976520000]], [[19332719318713200000], [(-89135699169847621627973277810124447/1050573335467750)], [(69638596996899431905424148580124447/525286667733875)], [(-87849325884775782435750888650124447/1050573335467750)], [16658333520120000000]], [[-10241621700000000000], [60653788956800000000], [-109332570221600000000], [74639519284800000000], [-15719116320000000000]], [[], [-13905800000000000000], [33373920000000000000], [-25030440000000000000], [5562320000000000000]]]
noncomputable def numerator (p u dummy : ℝ) : ℝ := numeratorPolynomial.eval p u dummy
def denominatorPolynomial : RationalPolynomial3 := [[[959396339712000000], [-920317059072000000]], [[], [1302642688000000000]]]
noncomputable def denominator (p u dummy : ℝ) : ℝ := denominatorPolynomial.eval p u dummy
noncomputable def target (p u : ℝ) : ℝ := capCore (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) (p+(527/2000)+u*((97/100)-p-(527/2000))) (8793/100000) (-3589/10000) 0
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

end OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0CapZeroTriangle


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadSquare
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

end OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadSquare


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1CapFlat
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

end OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1CapFlat
