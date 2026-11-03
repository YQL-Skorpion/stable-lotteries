import OptimalG.Certificates.DenseBernstein
import OptimalG.Certificates.ExtendedScalarExpressions

/-! An exact endpoint polynomial sign for C.4. -/
namespace OptimalG.Certificates.ExtendedCoefficientData.ThetaSlackLo
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numeratorPolynomial : RationalPolynomial3 := [[[0, (31/100), (-649051/1000000), (31/100)], [(-29051/500000), (31/50)]], [[(19/200), (-375949/500000), (81/200)], [(-43/100)]], [[(-19/100), (81/100)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-123682044731/100000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(9/25), (19/50)⟩]
def numeratorScale : ℚ := 200000000000000
def numeratorCertificate : DenseBernstein3 := [[[363623410373, 989225925944, 880660870769, 255554355198], [353865413738, 961529464039, 854541936864, 247373886563]], [[727228121209, 1978404766647, 1761283831667, 511099186229], [707711854416, 1923011022268, 1709045143288, 494737975436]], [[363604711344, 989178842308, 880622962584, 255544831620], [353846441186, 961481559834, 854503208110, 247364089462]]]
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
  have he : numeratorReduced.eval lam S p=numerator lam S p-(123682044731/100000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval lam S p at hh
  rw [he] at hh
  have hm : (0:ℝ)<(123682044731/100000000000000) := by norm_num
  linarith only [hh,hm]

 theorem expression_identity (lam S p : ℝ) :
    numerator lam S p=ExtendedScalarExpressions.thetaSlack lam S p (1529/5000) := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,ExtendedScalarExpressions.thetaSlack,
    ExtendedScalarExpressions.denominator,ExtendedScalarExpressions.etaNumerator,
    ExtendedScalarExpressions.betaNumerator,ExtendedScalarExpressions.denominatorDerivative,
    ExtendedScalarExpressions.etaNumeratorDerivative,SmallMassExpressions.initial,
    headInitial,Variational.cap,Variational.capScore,Variational.quadratic]
  <;> ring

end OptimalG.Certificates.ExtendedCoefficientData.ThetaSlackLo
