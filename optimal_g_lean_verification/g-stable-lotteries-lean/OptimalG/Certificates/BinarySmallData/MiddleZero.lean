import OptimalG.Certificates.DenseBernstein
import OptimalG.Certificates.SmallMassExpressions

namespace OptimalG.Certificates.BinarySmallData.MiddleZero
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numeratorPolynomial : RationalPolynomial3 := [[[0, (1/2), -1, (1/2)], [0, 1]], [[0, -1, (1/2)], [-1]], [[0, 1]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-354716993/800000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(527/2000), (16/25)⟩]
def numeratorScale : ℚ := 80000000000000
def numeratorCertificate : DenseBernstein3 := [[[1512292968125, 4594809246300, 983199092475, 35471699300], [1497086361525, 4568348758500, 975897936675, 39424424700]], [[3024603873650, 9189730760190, 1966597258380, 71048141840], [2994190406010, 9136809021270, 1951994183460, 78953338200]], [[1512310906052, 4594921516224, 983398168992, 35576443820], [1497104045012, 4568460265104, 976096249872, 39528914780]]]
noncomputable def numerator (lam S p : ℝ) : ℝ := numeratorPolynomial.eval lam S p

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {lam S p : ℝ}
    (hlam : lam∈Icc (22493/40000) (56233/100000))
    (hS : S∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (527/2000) (16/25))
    : 0<numerator lam S p := by
  have hx : ∀ i,(numeratorBox i).Contains (![lam, S, p] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hlam
    · simpa [numeratorBox,RatInterval.Contains] using hS
    · simpa [numeratorBox,RatInterval.Contains] using hp
  have hh := DenseBernstein3.scaledBoxCheck_sound numeratorChecked ![lam, S, p] hx
  have he : numeratorReduced.eval lam S p=numerator lam S p-(354716993/800000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval lam S p at hh
  rw [he] at hh
  have hm : (0:ℝ)<(354716993/800000000000) := by norm_num
  linarith only [hh,hm]

theorem expression_identity (lam S p : ℝ) : numerator lam S p=lam*(Variational.quadratic lam p-S)-p*(Variational.quadratic lam (1-p)-S) := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,
    SmallMassExpressions.initial,SmallMassExpressions.slope,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic]
  <;> ring

end OptimalG.Certificates.BinarySmallData.MiddleZero
