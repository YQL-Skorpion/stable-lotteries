import OptimalG.Certificates.DenseBernstein
import OptimalG.Certificates.ExtendedScalarExpressions

/-! An exact endpoint polynomial sign for C.4. -/
namespace OptimalG.Certificates.ExtendedCoefficientData.AlphaSlackHi
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numeratorPolynomial : RationalPolynomial3 := [[[0, (84/25), (-273/50), 3], [(27/25), 6]], [[(-3/2), (-102/25), (3/2)], [-9]], [[2, 3]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-1011963697/160000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(9/25), (19/50)⟩]
def numeratorScale : ℚ := 4000000000000
def numeratorCertificate : DenseBernstein3 := [[[32280496645, 96294339285, 93544768635, 29626925995], [27647335075, 82700182575, 80255939925, 25299092425]], [[64570694508, 192617931804, 187118952084, 59263714788], [55304256870, 165429274890, 160540951170, 50607933150]], [[32290198171, 96323593449, 93574184385, 29636789107], [27656922103, 82729093245, 80285012181, 25308841039]]]
noncomputable def numerator (lam S p : ℝ) : ℝ := numeratorPolynomial.eval lam S p

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {lam S p : ℝ}
    (hlam : lam∈Icc (22493/40000) (56233/100000))
    (hS : S∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (9/25) (19/50))
    : 0<numerator lam S p := by
  have hx : ∀ i,(numeratorBox i).Contains (![lam, S, p] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hlam
    · simpa [numeratorBox,RatInterval.Contains] using hS
    · simpa [numeratorBox,RatInterval.Contains] using hp
  have hh := DenseBernstein3.scaledBoxCheck_sound numeratorChecked ![lam, S, p] hx
  have he : numeratorReduced.eval lam S p=numerator lam S p-(1011963697/160000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval lam S p at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1011963697/160000000000) := by norm_num
  linarith only [hh,hm]

 theorem expression_identity (lam S p : ℝ) :
    numerator lam S p=ExtendedScalarExpressions.alphaSlack lam S p (9/25) := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,ExtendedScalarExpressions.alphaSlack,
    ExtendedScalarExpressions.denominator,ExtendedScalarExpressions.etaNumerator,
    ExtendedScalarExpressions.betaNumerator,ExtendedScalarExpressions.denominatorDerivative,
    ExtendedScalarExpressions.etaNumeratorDerivative,SmallMassExpressions.initial,
    headInitial,Variational.cap,Variational.capScore,Variational.quadratic]
  <;> ring

end OptimalG.Certificates.ExtendedCoefficientData.AlphaSlackHi
