import OptimalG.Certificates.ScaledTensorReconstruction5
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper0Head
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

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper0Head


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper0Cap
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-294998151896075993629368057429294560526839290368729/131321666933468750000000000000000), (332102093509332988671339696522657045359700669168729/131321666933468750000000000000000), (-92759854033142487604929097733406212082153447/328304167333671875000000000)], [(28493363814171411093861383132543693974083483819/5252866677338750000000000000), (-28493363814171411093861383132543693974083483819/5252866677338750000000000000)], [(-243355926814130731407918116755983769474136127/67236693469936000000000000), (243355926814130731407918116755983769474136127/67236693469936000000000000)]], [[(2629796380494906737544392353845254909450981079485151/32830416733367187500000000000000), (-27880292199800903935674993658903363503723087167/328304167333671875000000000), (6421910009703777506247452829919756495747843/8207604183341796875000000), (8610085269888390468975323667390315403897/2051901045835449218750)], [(-1874590576139233861695786659045524713451164157/8207604183341796875000000), (1943471258298340985447589248384647236682340157/8207604183341796875000000), (-8610085269888390468975323667390315403897/1025950522917724609375)], [(3314077199103694962452914920959907799034449/16415208366683593750000), (-3314077199103694962452914920959907799034449/16415208366683593750000)], [-52372429439309111250, 52372429439309111250]], [[(-412740276009582889197031066597455627486335843/8207604183341796875000000), (394193248460347612988275148577583104255159843/8207604183341796875000000), (2318378443654409526094489752484065403897/1025950522917724609375)], [(129400413613291329286209694977407893528897/1025950522917724609375), (-129400413613291329286209694977407893528897/1025950522917724609375)], [-78558644158963666875, 78558644158963666875]], [[(3973328382579571416786344162422184596103/2051901045835449218750), (-3973328382579571416786344162422184596103/2051901045835449218750)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[12265127188279702272, -12265127188279702272]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) (p-z+r) (Variational.cap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
theorem identity (p z r : ℝ) (hr : r≠1) :
    numerator p z r= -target p z r * denominator p z r := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,core,massCap,massLower,
    SmallMassExpressions.primitive,SmallMassExpressions.initial,SmallMassExpressions.slope,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic,
    lateHeadCone,lateHeadNearLine,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  have hd : (1:ℝ)-r≠0 := sub_ne_zero.mpr (Ne.symm hr)
  field_simp [hd]
  <;> ring
theorem nonpos {p z r : ℝ} (hr : r≠1)
    (hn : 0≤numerator p z r) (hd : 0<denominator p z r) :
    target p z r≤0 := by
  rw [identity p z r hr] at hn
  have hh := (nonneg_of_mul_nonneg_left hn hd)
  linarith only [hh]

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper0Cap


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper0Cone
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

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper0Cone


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper0NearLine
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

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper0NearLine


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper0Line
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

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper0Line
