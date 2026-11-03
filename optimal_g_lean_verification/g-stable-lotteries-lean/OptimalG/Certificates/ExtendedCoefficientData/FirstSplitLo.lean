import OptimalG.Certificates.DenseBernstein
import OptimalG.Certificates.ExtendedScalarExpressions

/-! An exact endpoint polynomial sign for C.4. -/
namespace OptimalG.Certificates.ExtendedCoefficientData.FirstSplitLo
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numeratorPolynomial : RationalPolynomial3 := [[[0, (-4029/5000), (11529/10000), (-1/2)], [(-1529/5000), -1]], [[(1/2), (8533349/5270000)], [2, (2958920800/1143447183)]], [[0, (-8751/2635)]], [[(-4527/1054)], [(-9676000000/1143447183)]], [[(4000/527)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-10520950005371762871339/2032794992000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(9/25), (56233/100000)⟩]
def numeratorScale : ℚ := 457378873200000000000000000
def numeratorCertificate : DenseBernstein3 := [[[20616514679649846231852475, 34143630226519378757383925, 17913603980097121896902425, 2492283561935062833836775], [20464652797890048951194975, 33714836652273368008283425, 17511602476884492240673925, 2367213751208646646051275]], [[82468223502016056381549775, 136580063460761320857702325, 71659006679506084881523325, 9970347235590714255233975], [81860768562095480506683275, 134864867686771835923891625, 70050979951288842638501425, 9470061341442381071156275]], [[123705582492580841925057600, 204878409208779540340860660, 107495396335863973372700520, 14957340391910115731692260], [122794388963274066299397000, 202305583331975654979013260, 105083325170176529525987520, 14206901573719781621166060]], [[82472553197713619157164120, 136591148941354791711015080, 71668188553600338261305800, 9972773324789059557318040], [81865083431822606100067240, 134875910212731431869114840, 70060120394026657748795960, 9472474127947725829611560]], [[20618679527498987383973549, 34149172966817193476982007, 17918194917145327879735367, 2493496606534595249192709], [20466810232753971358328269, 33720357915254244812218967, 17516172698254478627145127, 2368420144461678635720229]]]
noncomputable def numerator (lam S p : ℝ) : ℝ := numeratorPolynomial.eval lam S p

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {lam S p : ℝ}
    (hlam : lam∈Icc (22493/40000) (56233/100000))
    (hS : S∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (9/25) (56233/100000))
    : 0<numerator lam S p := by
  have hx : ∀ i,(numeratorBox i).Contains (![lam, S, p] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hlam
    · simpa [numeratorBox,RatInterval.Contains] using hS
    · simpa [numeratorBox,RatInterval.Contains] using hp
  have hh := DenseBernstein3.scaledBoxCheck_sound numeratorChecked ![lam, S, p] hx
  have he : numeratorReduced.eval lam S p=numerator lam S p-(10520950005371762871339/2032794992000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval lam S p at hh
  rw [he] at hh
  have hm : (0:ℝ)<(10520950005371762871339/2032794992000000000000000) := by norm_num
  linarith only [hh,hm]

 theorem expression_identity (lam S p : ℝ) :
    numerator lam S p=ExtendedScalarExpressions.firstSplit lam S p (1529/5000) := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,ExtendedScalarExpressions.firstSplit,
    ExtendedScalarExpressions.denominator,ExtendedScalarExpressions.etaNumerator,
    ExtendedScalarExpressions.betaNumerator,ExtendedScalarExpressions.denominatorDerivative,
    ExtendedScalarExpressions.etaNumeratorDerivative,SmallMassExpressions.initial,
    headInitial,Variational.cap,Variational.capScore,Variational.quadratic]
  <;> ring

end OptimalG.Certificates.ExtendedCoefficientData.FirstSplitLo
