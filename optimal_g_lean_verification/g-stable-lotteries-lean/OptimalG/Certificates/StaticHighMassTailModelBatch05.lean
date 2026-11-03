import OptimalG.Certificates.ScaledTensorReconstruction5
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0CapFlat
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-46512760825713826556825847246326143290468881/23117859287970064611624000000000000000000000)], [(1558900202795876814897954685277825286497/308238123839600861488320000000000000000)], [(-13314244191605251104900688827108780701/3945447985146891027050496000000000000)]], [[(1043130600611597111282845711116292762846825497976021/92211255245285224698861501856866000000000000000000)], [(-3041264753121996342630036200004554363679806069/100667309219743695086093342638500000000000000)], [(4899773976270149873973548845065376549034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-782682036928770831658208754067622477257693931/100667309219743695086093342638500000000000000)], [(224367951217076736149106414240689143528897/12583413652467961885761667829812500000000)], [(-671345950625/58679982336)]], [[(174407730781350603221506819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := capCore (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) ((313/1000)-z+p)
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

end OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0CapFlat


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0HeadZero
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-48418924681663620587943608916067296132660481/23117859287970064611624000000000000000000000)], [(4920299823205495496593897496055987404819/924714371518802584464960000000000000000)], [(-13314244191605251104900688827108780701/3945447985146891027050496000000000000)]], [[(314070943014603866333/27506241720000000000)], [(-20792975056554445802338150631411813192491269/657956269410089510366623154500000000000000)], [(5037535340588364121477154023743621595496801/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-4384068370854776144414386312041795245008731/657956269410089510366623154500000000000000)], [(24265126781984507961201066675923862524567/1398157072496440209529074203312500000000)], [(-671345950625/58679982336)]], [[(108293424099618781603825118132872771/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := headLow (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) 0
theorem identity (p z : ℝ) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0HeadZero


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0HeadCapBoundary
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-46814214854050934558552138628601501327812281/23117859287970064611624000000000000000000000)], [(1558900202795876814897954685277825286497/308238123839600861488320000000000000000)], [(-13314244191605251104900688827108780701/3945447985146891027050496000000000000)]], [[(657207341223773872612643456446128471583/57794648219925161529060000000000000000)], [(-10535205352556651021646195253207062036608129/348329789687694446664682846500000000000000)], [(4899773976270149873973548845065376549034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-2711843715794730218486496345444943900891871/348329789687694446664682846500000000000000)], [(224367951217076736149106414240689143528897/12583413652467961885761667829812500000000)], [(-671345950625/58679982336)]], [[(174407730781350603221506819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := headLow (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) ((527/2000)-z+p)
theorem identity (p z : ℝ) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0HeadCapBoundary


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower1HeadSquare
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-36669169118411391045002786505191449837422018324567700532828675161/528402076731425941265757795165536400000000000000000000000000000000)]], [[(-49199258306854354791853981781353238528746650047811608320725943301714172080297/107612273199798089338934595645612508241020974750000000000000000000000000000000)], [(359459057374911803608389142106872460395501855944844554591906030858468613577/146352691551725401500951050078033011207788525660000000000000000000000000000)], [(-603648919111935135127150270528534171409758617860590226352481122329901079/312219075310347523202028906833137090576615521408000000000000000000000000)]], [[(461401414635094047573885987674191118803066755625365625205826036084742832578121495621/100997167376547076723855358047305766123394177650152591750000000000000000000000000000)], [(-2623340198573177169162787474809244339587014718245293/174134311488312643759924264096077300000000000000000)], [(4941247318281734257257622046556006286935637995227/371486531175066973354505096738298240000000000000)], [(-3152346095875039749952404233859018478091/1288541558012719297101994785772800000000)]], [[(-165370367899913829901591847232422136765347057967121/43533577872078160939981066024019325000000000000000)], [(33766077074878186986796846155867667609424322509/3482686229766252875198485281921546000000000000)], [(-48700594835173489097014693008887976468027859/7429730623501339467090101934765964800000000)]], [[(416589928088877360721174205096908403621/1368859907683542359162748752437500000000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := headCleared (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000)
theorem identity (p z : ℝ) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower1HeadSquare


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower1CapFlat
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-39939590000138385914516708194723020165000131/23117859287970064611624000000000000000000000)], [(2749527863584958928395524175384212333919/616476247679201722976640000000000000000)], [(-12079121076993306885558983309485175651/3945447985146891027050496000000000000)]], [[(894471116168830777965261219221477405432762997976021/92211255245285224698861501856866000000000000000000)], [(-2663886646864594038955021191924027008211056069/100667309219743695086093342638500000000000000)], [(4389849557964677776253977962908294029503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-685641773471996579714267039452681071007693931/100667309219743695086093342638500000000000000)], [(198882773394973222243100582260928401341397/12583413652467961885761667829812500000000)], [(-609067169375/58679982336)]], [[(174407730781350603221506819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := capCore (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) ((313/1000)-z+p)
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

end OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower1CapFlat
