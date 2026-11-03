import OptimalG.Certificates.DenseBernstein
import OptimalG.Certificates.ExtendedScalarExpressions

/-! An exact endpoint polynomial sign for C.4. -/
namespace OptimalG.Certificates.ExtendedCoefficientData.ThetaSlackHi
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numeratorPolynomial : RationalPolynomial3 := [[[0, (31/100), (-3271/5000), (31/100)], [(-171/2500), (31/50)]], [[(19/200), (-927/1250), (81/200)], [(-43/100)]], [[(-19/100), (81/100)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-184507902591/100000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(9/25), (19/50)⟩]
def numeratorScale : ℚ := 200000000000000
def numeratorCertificate : DenseBernstein3 := [[[478659073013, 1342667085264, 1242024281489, 378512269238], [467590964818, 1311040288679, 1211975012904, 369021689043]], [[957303153769, 2685298413087, 2484022186867, 757018927549], [935166663856, 2622043999348, 2423922829128, 738037493636]], [[478644081264, 1342631329428, 1241997907064, 378506658900], [467575699546, 1311003712274, 1211947817910, 369015805182]]]
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
  have he : numeratorReduced.eval lam S p=numerator lam S p-(184507902591/100000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval lam S p at hh
  rw [he] at hh
  have hm : (0:ℝ)<(184507902591/100000000000000) := by norm_num
  linarith only [hh,hm]

 theorem expression_identity (lam S p : ℝ) :
    numerator lam S p=ExtendedScalarExpressions.thetaSlack lam S p (9/25) := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,ExtendedScalarExpressions.thetaSlack,
    ExtendedScalarExpressions.denominator,ExtendedScalarExpressions.etaNumerator,
    ExtendedScalarExpressions.betaNumerator,ExtendedScalarExpressions.denominatorDerivative,
    ExtendedScalarExpressions.etaNumeratorDerivative,SmallMassExpressions.initial,
    headInitial,Variational.cap,Variational.capScore,Variational.quadratic]
  <;> ring

end OptimalG.Certificates.ExtendedCoefficientData.ThetaSlackHi
