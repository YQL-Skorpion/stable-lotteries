import OptimalG.Certificates.ScaledTensorReconstruction5
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadZeroTriangle
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-314538455133100217790839649216482910741/171065209206854449664000000000000000000000)], [(232046212804321553724540530007092289809/6842608368274177986560000000000000000000)], [(-548008045151278876233367656802272733713/5474086694619342389248000000000000000000)]], [[(11570771949545087759203693451216362272914177/1610676947515899121377493482216000000000000000)], [(-4248148153993927362930499044300882835922435989751/5726851368945419098231087936768000000000000000000)], [(233177300304416922886781561857376801882407630263787/103083324641017543768159582861824000000000000000000)], [(115388936569793/130264268800000)]], [[(-1124333556981553452237298171008013085456901/5592628289985760838116296813250000000000000)], [(229204735990437109374339814045085663992135217/100667309219743695086093342638500000000000000)], [(-903834321608205473325131327666959844891797335101/103083324641017543768159582861824000000000000000)], [(-283047268773/65132134400)]], [[(108293424099618781603825118132872771/316535994377047602997513875000000000)], [(-95026469809253357657462021473607404193713/50333654609871847543046671319250000000000)], [(2472462410193006332216690989608050306434301/201334618439487390172186685277000000000000)], [(1157184255/162830336)]], [[], [], [(-118273125/20353792)], [(-39424375/10176896)]]]
noncomputable def numerator (p u dummy : ℝ) : ℝ := numeratorPolynomial.eval p u dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p u dummy : ℝ) : ℝ := denominatorPolynomial.eval p u dummy
noncomputable def target (p u : ℝ) : ℝ := headLow (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) ((7/8)+u*(p-1223/2000)) (8793/100000) (-1757/5000) 0
theorem identity (p u : ℝ) :
    numerator p u 0= -target p u * denominator p u 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadZeroTriangle


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadZeroRectangle
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

end OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadZeroRectangle


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadCapBoundaryTriangle
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-2724276082728054571202714568410065515541/171065209206854449664000000000000000000000)], [(328435717908119727861015526774835594001/6842608368274177986560000000000000000000)], [(-548008045151278876233367656802272733713/5474086694619342389248000000000000000000)]], [[(64211459837332034875726395441959557218389099/8053384737579495606887467411080000000000000000)], [(-8362195764779486225402716813315554950120257874149/17180554106836257294693263810304000000000000000000)], [(206802430840056183276628618459075005389596456553963/103083324641017543768159582861824000000000000000000)], [(115388936569793/130264268800000)]], [[(-872357963938388252258787817194614125846849/16777884869957282514348890439750000000000000)], [(25991961093562292879833321421672453459452769/20133461843948739017218668527700000000000000)], [(-817571461544883348680313851302931074678187609149/103083324641017543768159582861824000000000000000)], [(-283047268773/65132134400)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)], [(-51312614955082157677182767794109880962537/50333654609871847543046671319250000000000)], [(2334701045874792084713085810929805259971949/201334618439487390172186685277000000000000)], [(1157184255/162830336)]], [[], [], [(-118273125/20353792)], [(-39424375/10176896)]]]
noncomputable def numerator (p u dummy : ℝ) : ℝ := numeratorPolynomial.eval p u dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p u dummy : ℝ) : ℝ := denominatorPolynomial.eval p u dummy
noncomputable def target (p u : ℝ) : ℝ := headLow (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) ((7/8)+u*(p-1223/2000)) (8793/100000) (-1757/5000) ((527/2000)-((7/8)+u*(p-1223/2000))+p)
theorem identity (p u : ℝ) :
    numerator p u 0= -target p u * denominator p u 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadCapBoundaryTriangle


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadCapBoundaryRectangle
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

end OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadCapBoundaryRectangle


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1CapZeroRectangle
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-68574834745046884706067626951857290116126397/1050573335467750000000000000)], [(18177772536641617118628477270391491259917861/1050573335467750000000000000)], [(-62925482657779097851595017959116568205383/42022933418710000000000000)], [(355499999132356691840808330939353607003/8404586683742000000000000)]], [[(608081628128695810166932936922205779170157/262643333866937500000000)], [(-3333477627886298155820166041552299568103/5252866677338750000000)], [(126769173334810489046694011514642662697/2101146670935500000000)], [(-23369506433893719/10)], [30296717857395]], [[(-22250599795990608494982888802767118881/2101146670935500000)], [(4466965093609602243184906082537097603/2101146670935500000)], [-136030022983265400], [2754247077945000]], [[17116820871853200000], [-2254252256031600000], [74188473480000000]], [[-9291536700000000000], [624482100000000000]]]
noncomputable def numerator (p u dummy : ℝ) : ℝ := numeratorPolynomial.eval p u dummy
def denominatorPolynomial : RationalPolynomial3 := [[[959396339712000000], [-64480813056000000]]]
noncomputable def denominator (p u dummy : ℝ) : ℝ := denominatorPolynomial.eval p u dummy
noncomputable def target (p u : ℝ) : ℝ := capCore (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) (p+(527/2000)+u*((313/1000)-(527/2000))) (8793/100000) (-1757/5000) 0
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

end OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1CapZeroRectangle
