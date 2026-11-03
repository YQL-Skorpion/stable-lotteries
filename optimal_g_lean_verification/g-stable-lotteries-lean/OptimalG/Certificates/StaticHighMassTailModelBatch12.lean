import OptimalG.Certificates.ScaledTensorReconstruction5
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper1Head
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-423086167986637211308247225244094462619/2672893893857100776000000000000000000000), (1936100805801358073341014781/84045866837420000000000000000)], [(83398225653477946888564101069792693/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(37450232504442884599033144190692967/6682234734642751940000000000000000), (-56233/100000)], [(-3107335620010100942847406104400493089150691/191019562086800180429019625500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(2951253188005627461078870205013762779503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-680100673469455113574011110335060192099309/191019562086800180429019625500000000000000), (-29159425505356880854446649382872771/158267997188523801498756937500000000)], [(115132739137055113882426638417569026341397/12583413652467961885761667829812500000000)], [(-118273125/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3514/10000) (p-z+r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
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

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper1Head


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper1Cap
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-254950314022958348181357075114532160451822223649979/131321666933468750000000000000000), (292054255636215343223328714207894645284683602449979/131321666933468750000000000000000), (-92759854033142487604929097733406212082153447/328304167333671875000000000)], [(50255492682481873959279628521236777614947422613/10505733354677500000000000000), (-50255492682481873959279628521236777614947422613/10505733354677500000000000000)], [(-220780516151656897215263658140498212179939777/67236693469936000000000000), (220780516151656897215263658140498212179939777/67236693469936000000000000)]], [[(2247841119198839937333701241557466776638481079485151/32830416733367187500000000000000), (-24060739586840235933568082536025482175598087167/328304167333671875000000000), (6421910009703777506247452829919756495747843/8207604183341796875000000), (8610085269888390468975323667390315403897/2051901045835449218750)], [(-1637565871745323196880583017019059857982414157/8207604183341796875000000), (1706446553904430320632385606358182381213590157/8207604183341796875000000), (-8610085269888390468975323667390315403897/1025950522917724609375)], [(2951253188005627461078870205013762779503199/16415208366683593750000), (-2951253188005627461078870205013762779503199/16415208366683593750000)], [-47513993824191048750, 47513993824191048750]], [[(-358413054918402844853503855146576721236335843/8207604183341796875000000), (339866027369167568644747937126704198005159843/8207604183341796875000000), (2318378443654409526094489752484065403897/1025950522917724609375)], [(115132739137055113882426638417569026341397/1025950522917724609375), (-115132739137055113882426638417569026341397/1025950522917724609375)], [-71270990736286573125, 71270990736286573125]], [[(3973328382579571416786344162422184596103/2051901045835449218750), (-3973328382579571416786344162422184596103/2051901045835449218750)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[12265127188279702272, -12265127188279702272]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3514/10000) (p-z+r) (Variational.cap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
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

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper1Cap


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper1Cone
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-423086167986637211308247225244094462619/2672893893857100776000000000000000000000), (1936100805801358073341014781/84045866837420000000000000000)], [(83398225653477946888564101069792693/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(18738567268495534443191732236442967/3341117367321375970000000000000000), (-1390328941945788270803468804731354687/2402550241951025449696500000000000000), (1069761957651165231815925679627229/316535994377047602997513875000000000)], [(-3107335620010100942847406104400493089150691/191019562086800180429019625500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(2951253188005627461078870205013762779503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-680100673469455113574011110335060192099309/191019562086800180429019625500000000000000), (-29159425505356880854446649382872771/158267997188523801498756937500000000)], [(115132739137055113882426638417569026341397/12583413652467961885761667829812500000000)], [(-118273125/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3514/10000) (p-z+r) (lateHeadCone (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
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

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper1Cone


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper1NearLine
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-423086167986637211308247225244094462619/2672893893857100776000000000000000000000), (1936100805801358073341014781/84045866837420000000000000000)], [(83398225653477946888564101069792693/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(18802082744927655630725424736442967/3341117367321375970000000000000000), (-1650741362670859919296072439731354687/2402550241951025449696500000000000000), (49974573088905019894931819367127229/316535994377047602997513875000000000)], [(-3107335620010100942847406104400493089150691/191019562086800180429019625500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(2951253188005627461078870205013762779503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-680100673469455113574011110335060192099309/191019562086800180429019625500000000000000), (-29159425505356880854446649382872771/158267997188523801498756937500000000)], [(115132739137055113882426638417569026341397/12583413652467961885761667829812500000000)], [(-118273125/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3514/10000) (p-z+r) (lateHeadNearLine (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
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

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper1NearLine


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper1Line
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-423086167986637211308247225244094462619/2672893893857100776000000000000000000000), (1936100805801358073341014781/84045866837420000000000000000)], [(83398225653477946888564101069792693/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(18802083035604866587685134126442967/3341117367321375970000000000000000), (-1650741362670859919296072439731354687/2402550241951025449696500000000000000), (49974573088905019894931819367127229/316535994377047602997513875000000000)], [(-3107335620010100942847406104400493089150691/191019562086800180429019625500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(2951253188005627461078870205013762779503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-680100673469455113574011110335060192099309/191019562086800180429019625500000000000000), (-29159425505356880854446649382872771/158267997188523801498756937500000000)], [(115132739137055113882426638417569026341397/12583413652467961885761667829812500000000)], [(-118273125/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3514/10000) (p-z+r) (Variational.quadratic (StaticLow.lam:ℝ) r-(StaticLow.slack:ℝ)) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
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

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper1Line
