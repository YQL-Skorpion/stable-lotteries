import OptimalG.Certificates.DenseBernsteinHigher
import OptimalG.Certificates.ExtendedSelectedExpressions

namespace OptimalG.Certificates.ExtendedSelectedData.HeadLateInactive
open Set ExtendedSelectedExpressions
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numeratorPolynomial : RationalPolynomial5 := [[[[], [[(-1/2), (-7/8)]], [[1, (1/2)]], [[(-1/2)]]], [[[0, -1]], [[-1]]]], [[[[(1/2)]], [[0, (5581/1054)]]], [[[2]], [[0, (9676000000/1143447183)]]]], [[[[(-1/8)]], [[-1, (-4000/527)]]]], [[[[(-4527/1054)]]], [[[(-9676000000/1143447183)]]]], [[[[(4000/527)]]]]]
def numeratorReduced : RationalPolynomial5 := numeratorPolynomial.add [[[[[(-1811529897016138295197/731806197120000000000000)]]]]]
def numeratorBox : Fin 5→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(19/50), (9/20)⟩, ⟨0, 1⟩, ⟨(1529/5000), (9/25)⟩]
def numeratorScale : ℚ := 457378873200000000000000000
def numeratorCertificate : DenseBernstein5 := [[[[[7788357159029895965655625, 7230638332350542245655625]], [[15769210191034448990466875, 14426764978480317414466875]], [[9479719016401782083966875, 8528720411903808091966875]], [[1420425507643429059155625, 1254153289020232923155625]]], [[[7639143631051879052998125, 7094169491890322556998125]], [[15330838845336629540494375, 14031880194174731548494375]], [[9050616908940193921994375, 8148357364673295425994375]], [[1280481217901643434498125, 1132206185635086434498125]]]], [[[[31155177841583633197262375, 28924158927373558553262375]], [[63081759088335832378787125, 57711520961629521036787125]], [[37923465097611053165787125, 34118986949117566413787125]], [[5683121943843653984262375, 5017863007846403930262375]]], [[[30558316392076959629595875, 28378276481470862972795875]], [[61328251956264469750987625, 56131960882428868535387625]], [[36207035181988348613187625, 32597514128424348152387625]], [[5123337710785638491795875, 4530067820451142589795875]]]], [[[[46735390632814473051466500, 43388646848472861900106500]], [[94630016302871429167339500, 86573973192385477906219500]], [[56892081375834871180279500, 51184638551321170112119500]], [[8526812845255115064406500, 7528669346885754106006500]]], [[[45840087452058722139405900, 42569812553422261605645900]], [[91999722980532762928757700, 84204601660305540542837700]], [[54317404273424791439297700, 48902398372313096268737700]], [[7687125884427950649945900, 6796966404907017331545900]]]], [[[[31158676376998349898056720, 28927370244227936647336720]], [[63091596104875315733050160, 57720443413805820932810160]], [[37932643524445869771930160, 34127197902907031923610160]], [[5685961889553703936936720, 5020362826313947638136720]]], [[[30561800252094800818559840, 28381473629993943737439840]], [[61338045473620792416159520, 56140841450025559323119520]], [[36216170636647470376639520, 32605683818048487433919520]], [[5126163508106278779039840, 4532554091001671848239840]]]], [[[[7790106426737614080366699, 7232243990778091057006699]], [[15774128699305269960540097, 14431226204569546655420097]], [[9484308229820269679980097, 8532825888799620139820097]], [[1421845480498813799806699, 1255403198254364541406699]]], [[[7640885561061159257921419, 7095768066152222549761419]], [[15335735604015869704404257, 14036320477974155773684257]], [[9055184636270833635044257, 8152442209486443898084257]], [[1281894116562323188561419, 1133449320910710674161419]]]]]
noncomputable def numerator (lam S p z t : ℝ) : ℝ := numeratorPolynomial.eval lam S p z t

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {lam S p z t : ℝ}
    (hlam : lam∈Icc (22493/40000) (56233/100000))
    (hS : S∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (19/50) (9/20))
    (hz : z∈Icc 0 1)
    (ht : t∈Icc (1529/5000) (9/25))
    : 0<numerator lam S p z t := by
  have hx : ∀ i,(numeratorBox i).Contains (![lam, S, p, z, t] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hlam
    · simpa [numeratorBox,RatInterval.Contains] using hS
    · simpa [numeratorBox,RatInterval.Contains] using hp
    · simpa [numeratorBox,RatInterval.Contains] using hz
    · simpa [numeratorBox,RatInterval.Contains] using ht
  have hh := DenseBernstein5.scaledBoxCheck_sound numeratorChecked ![lam, S, p, z, t] hx
  have he : numeratorReduced.eval lam S p z t=numerator lam S p z t-(1811529897016138295197/731806197120000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial5.eval_add,numerator,RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval lam S p z t at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1811529897016138295197/731806197120000000000000) := by norm_num
  linarith only [hh,hm]

theorem expression_identity (lam S p z t : ℝ) :
    numerator lam S p z t = -(headLinear lam S p t (7/8)) := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial5.eval,RationalPolynomial4.eval,
    RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,
    capCoreCleared,headCore,headLinear,headGainCleared,highRankCore,
    ExtendedLocalExpressions.localCore,extendedNIncrement,extendedDIncrement,extendedWeightDifference,
    ExtendedScalarExpressions.denominator,ExtendedScalarExpressions.etaNumerator,
    ExtendedScalarExpressions.betaNumerator,Variational.quadratic,
    SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,headSlope,
    Variational.cap,Variational.capScore]
  <;> ring

end OptimalG.Certificates.ExtendedSelectedData.HeadLateInactive
