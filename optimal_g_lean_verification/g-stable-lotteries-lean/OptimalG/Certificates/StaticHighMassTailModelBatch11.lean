import OptimalG.Certificates.ScaledTensorReconstruction5
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighForwardKink
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-585734150493758517287728981924392449295713487975652404936976392892883164624187/22603864743850671720679220480000000000000000000000)], [(128117783191657206837171006684927763306064147619042858252937452142180470421/1808309179508053737654337638400000000000000000)], [(-531452208288551970796347581040387006322957819249065228448109561187509601/11573178748851543920987760885760000000000000)]], [[(799901524153467120696765691554232702691430692009881318850604467800558867349/5650966185962667930169805120000000000000000000)], [(-892817109600419004079161401006659811795406493471769/2151574191037952000000)], [(4677328239893028067588896491075879850111917447613/13770074822642892800)], [(-1000157363311051350269073570865789483204300875/17212593528303616)]], [[(-45244978024333417186147953824598133712217754503023/537893547759488000000)], [(9690716285846277588197993016055681270862621257/43031483820759040)], [(-5359497435238443395874754629311682874097552625/34425187056607232)]], [[(10085069387247326014152822004004670263146131/1344733869398720)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[(10085069387247326014152822004004670263146131/672366934699360)]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := flatHigh (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) (kink (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) 0
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

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighForwardKink


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0Head
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-489544945756025172411070274336836181369/2672893893857100776000000000000000000000), (1936100805801358073341014781/84045866837420000000000000000)], [(47284303827534513663328459687070859/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(43788721965159355955426972315692967/6682234734642751940000000000000000), (-56233/100000)], [(-3557097867436876397904718518112950120400691/191019562086800180429019625500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(3314077199103694962452914920959907799034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-783188379524825216692658570393653942099309/191019562086800180429019625500000000000000), (-29159425505356880854446649382872771/158267997188523801498756937500000000)], [(129400413613291329286209694977407893528897/12583413652467961885761667829812500000000)], [(-130366875/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) (p-z+r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
theorem identity (p z r : ℝ) :
    numerator p z r= -target p z r * denominator p z r := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,core,massCap,massLower,
    SmallMassExpressions.primitive,SmallMassExpressions.initial,SmallMassExpressions.slope,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic,
    lateHeadCone,lateHeadNearLine,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring
theorem nonpos {p z r : ℝ}
    (hn : 0≤numerator p z r) (hd : 0<denominator p z r) :
    target p z r≤0 := by
  rw [identity p z r] at hn
  have hh := (nonneg_of_mul_nonneg_left hn hd)
  linarith only [hh]

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0Head


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0Cone
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-489544945756025172411070274336836181369/2672893893857100776000000000000000000000), (1936100805801358073341014781/84045866837420000000000000000)], [(47284303827534513663328459687070859/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(21907811998853770121388646298942967/3341117367321375970000000000000000), (-1390328941945788270803468804731354687/2402550241951025449696500000000000000), (1069761957651165231815925679627229/316535994377047602997513875000000000)], [(-3557097867436876397904718518112950120400691/191019562086800180429019625500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(3314077199103694962452914920959907799034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-783188379524825216692658570393653942099309/191019562086800180429019625500000000000000), (-29159425505356880854446649382872771/158267997188523801498756937500000000)], [(129400413613291329286209694977407893528897/12583413652467961885761667829812500000000)], [(-130366875/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) (p-z+r) (lateHeadCone (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
theorem identity (p z r : ℝ) :
    numerator p z r= -target p z r * denominator p z r := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,core,massCap,massLower,
    SmallMassExpressions.primitive,SmallMassExpressions.initial,SmallMassExpressions.slope,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic,
    lateHeadCone,lateHeadNearLine,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring
theorem nonpos {p z r : ℝ}
    (hn : 0≤numerator p z r) (hd : 0<denominator p z r) :
    target p z r≤0 := by
  rw [identity p z r] at hn
  have hh := (nonneg_of_mul_nonneg_left hn hd)
  linarith only [hh]

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0Cone


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0NearLine
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-489544945756025172411070274336836181369/2672893893857100776000000000000000000000), (1936100805801358073341014781/84045866837420000000000000000)], [(47284303827534513663328459687070859/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(21971327475285891308922338798942967/3341117367321375970000000000000000), (-1650741362670859919296072439731354687/2402550241951025449696500000000000000), (49974573088905019894931819367127229/316535994377047602997513875000000000)], [(-3557097867436876397904718518112950120400691/191019562086800180429019625500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(3314077199103694962452914920959907799034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-783188379524825216692658570393653942099309/191019562086800180429019625500000000000000), (-29159425505356880854446649382872771/158267997188523801498756937500000000)], [(129400413613291329286209694977407893528897/12583413652467961885761667829812500000000)], [(-130366875/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) (p-z+r) (lateHeadNearLine (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
theorem identity (p z r : ℝ) :
    numerator p z r= -target p z r * denominator p z r := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,core,massCap,massLower,
    SmallMassExpressions.primitive,SmallMassExpressions.initial,SmallMassExpressions.slope,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic,
    lateHeadCone,lateHeadNearLine,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring
theorem nonpos {p z r : ℝ}
    (hn : 0≤numerator p z r) (hd : 0<denominator p z r) :
    target p z r≤0 := by
  rw [identity p z r] at hn
  have hh := (nonneg_of_mul_nonneg_left hn hd)
  linarith only [hh]

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0NearLine


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0Line
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-489544945756025172411070274336836181369/2672893893857100776000000000000000000000), (1936100805801358073341014781/84045866837420000000000000000)], [(47284303827534513663328459687070859/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(21971327765963102265882048188942967/3341117367321375970000000000000000), (-1650741362670859919296072439731354687/2402550241951025449696500000000000000), (49974573088905019894931819367127229/316535994377047602997513875000000000)], [(-3557097867436876397904718518112950120400691/191019562086800180429019625500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(3314077199103694962452914920959907799034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-783188379524825216692658570393653942099309/191019562086800180429019625500000000000000), (-29159425505356880854446649382872771/158267997188523801498756937500000000)], [(129400413613291329286209694977407893528897/12583413652467961885761667829812500000000)], [(-130366875/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) (p-z+r) (Variational.quadratic (StaticLow.lam:ℝ) r-(StaticLow.slack:ℝ)) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
theorem identity (p z r : ℝ) :
    numerator p z r= -target p z r * denominator p z r := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,core,massCap,massLower,
    SmallMassExpressions.primitive,SmallMassExpressions.initial,SmallMassExpressions.slope,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic,
    lateHeadCone,lateHeadNearLine,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring
theorem nonpos {p z r : ℝ}
    (hn : 0≤numerator p z r) (hd : 0<denominator p z r) :
    target p z r≤0 := by
  rw [identity p z r] at hn
  have hh := (nonneg_of_mul_nonneg_left hn hd)
  linarith only [hh]

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0Line
