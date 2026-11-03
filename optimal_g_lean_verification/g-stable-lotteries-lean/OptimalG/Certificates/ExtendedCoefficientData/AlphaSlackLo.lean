import OptimalG.Certificates.DenseBernstein
import OptimalG.Certificates.ExtendedScalarExpressions

/-! An exact endpoint polynomial sign for C.4. -/
namespace OptimalG.Certificates.ExtendedCoefficientData.AlphaSlackLo
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numeratorPolynomial : RationalPolynomial3 := [[[0, (16529/5000), (-55413/10000), 3], [(4587/5000), 6]], [[(-3/2), (-19587/5000), (3/2)], [-9]], [[2, 3]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-900912233/160000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(9/25), (19/50)⟩]
def numeratorScale : ℚ := 4000000000000
def numeratorCertificate : DenseBernstein3 := [[[31752165885, 93005190605, 88421383555, 27264358835], [26705284875, 78169875575, 73891396525, 22522805825]], [[63515203708, 186043211644, 176875824164, 54539816228], [53421327190, 156372238090, 147815506610, 45056595710]], [[31763038131, 93038021969, 88454441545, 27275457707], [26716042623, 78202363445, 73924111021, 22533790199]]]
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
  have he : numeratorReduced.eval lam S p=numerator lam S p-(900912233/160000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval lam S p at hh
  rw [he] at hh
  have hm : (0:ℝ)<(900912233/160000000000) := by norm_num
  linarith only [hh,hm]

 theorem expression_identity (lam S p : ℝ) :
    numerator lam S p=ExtendedScalarExpressions.alphaSlack lam S p (1529/5000) := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,ExtendedScalarExpressions.alphaSlack,
    ExtendedScalarExpressions.denominator,ExtendedScalarExpressions.etaNumerator,
    ExtendedScalarExpressions.betaNumerator,ExtendedScalarExpressions.denominatorDerivative,
    ExtendedScalarExpressions.etaNumeratorDerivative,SmallMassExpressions.initial,
    headInitial,Variational.cap,Variational.capScore,Variational.quadratic]
  <;> ring

end OptimalG.Certificates.ExtendedCoefficientData.AlphaSlackLo
