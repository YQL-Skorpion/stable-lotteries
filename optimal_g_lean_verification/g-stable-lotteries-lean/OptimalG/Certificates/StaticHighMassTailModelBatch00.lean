import OptimalG.Certificates.ScaledTensorReconstruction5
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadSquare
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

end OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadSquare


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0CapFlat
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

end OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0CapFlat


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadZeroTriangle
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-334011696534700096000063783977069004491/171065209206854449664000000000000000000000)], [(213917588184878543033584931991170787359/6842608368274177986560000000000000000000)], [(-604043364215083767745681126996388986863/5474086694619342389248000000000000000000)]], [[(15920900083946846726997837890616104948695427/1610676947515899121377493482216000000000000000)], [(-3835658377880134343046068523970422760771314631001/5726851368945419098231087936768000000000000000000)], [(266011698316739662863980912082385291106570397270037/103083324641017543768159582861824000000000000000000)], [(127187770426943/130264268800000)]], [[(-569075869505738793193760632557915844486263/2796314144992880419058148406625000000000000)], [(212271766452422941829471875511806916921822717/100667309219743695086093342638500000000000000)], [(-1025661477282925859515216069150777171428571878851/103083324641017543768159582861824000000000000000)], [(-311989624923/65132134400)]], [[(108293424099618781603825118132872771/316535994377047602997513875000000000)], [(-90293174783179465068224881133604962787463/50333654609871847543046671319250000000000)], [(2772242281137553832044114653510860365028051/201334618439487390172186685277000000000000)], [(1275509505/162830336)]], [[], [], [(-130366875/20353792)], [(-43455625/10176896)]]]
noncomputable def numerator (p u dummy : ℝ) : ℝ := numeratorPolynomial.eval p u dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p u dummy : ℝ) : ℝ := denominatorPolynomial.eval p u dummy
noncomputable def target (p u : ℝ) : ℝ := headLow (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) ((7/8)+u*(p-1223/2000)) (8793/100000) (-3589/10000) 0
theorem identity (p u : ℝ) :
    numerator p u 0= -target p u * denominator p u 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadZeroTriangle


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadZeroRectangle
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

end OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadZeroRectangle


namespace OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadCapBoundaryTriangle
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-2743749324129654449411938703170651609291/171065209206854449664000000000000000000000)], [(310307093288676717170059928758914091551/6842608368274177986560000000000000000000)], [(-604043364215083767745681126996388986863/5474086694619342389248000000000000000000)]], [[(85962100509340829714697117638958270597295349/8053384737579495606887467411080000000000000000)], [(-7124726436438107165749425252324174724666893797899/17180554106836257294693263810304000000000000000000)], [(239636828852378923253827968684083494613759223560213/103083324641017543768159582861824000000000000000000)], [(127187770426943/130264268800000)]], [[(-228453127507040163677364274879517484098431/4194471217489320628587222609937500000000000)], [(22605367185959459370859733715016704045390269/20133461843948739017218668527700000000000000)], [(-939398617219603734870398592786748401214962152899/103083324641017543768159582861824000000000000000)], [(-311989624923/65132134400)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)], [(-46579319929008265087945627454107439556287/50333654609871847543046671319250000000000)], [(2634480916819339584540509474832615318565699/201334618439487390172186685277000000000000)], [(1275509505/162830336)]], [[], [], [(-130366875/20353792)], [(-43455625/10176896)]]]
noncomputable def numerator (p u dummy : ℝ) : ℝ := numeratorPolynomial.eval p u dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p u dummy : ℝ) : ℝ := denominatorPolynomial.eval p u dummy
noncomputable def target (p u : ℝ) : ℝ := headLow (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) ((7/8)+u*(p-1223/2000)) (8793/100000) (-3589/10000) ((527/2000)-((7/8)+u*(p-1223/2000))+p)
theorem identity (p u : ℝ) :
    numerator p u 0= -target p u * denominator p u 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,headCleared,capCore,headLow,
    base,headLinear,splitLinear,flat,massCap,massLower,Variational.capDeficit,Variational.cap,
    Variational.quadratic,SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,
    headSlope,Variational.capScore,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadCapBoundaryTriangle
