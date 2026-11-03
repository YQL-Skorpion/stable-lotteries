import OptimalG.Certificates.DenseBernstein
import OptimalG.Certificates.ExtendedScalarExpressions

namespace OptimalG.Certificates.ExtendedCoefficientData.BinaryGap
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numeratorPolynomial : RationalPolynomial3 := [[[0, (1/2), -1, (1/2)], [0, 1]], [[0, -1, (1/2)], [-1]], [[0, 1]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-4368309168371/2000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(9/25), (56233/100000)⟩]
def numeratorScale : ℚ := 4000000000000000
def numeratorCertificate : DenseBernstein3 := [[[59137969293258, 139731406708199, 72764315773009, 8736618336742], [58623173563258, 138701827970199, 72249545487009, 8736631058742]], [[118277677708516, 279469991967088, 145538180655687, 17477346354463], [117248073526516, 277410796325088, 144508601917687, 17477359076463]], [[59139708451258, 139738585387122, 72773865031144, 8740728073954], [58624899999258, 138708968483122, 72259056579144, 8740728073954]]]
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
  have he : numeratorReduced.eval lam S p=numerator lam S p-(4368309168371/2000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval lam S p at hh
  rw [he] at hh
  have hm : (0:ℝ)<(4368309168371/2000000000000000) := by norm_num
  linarith only [hh,hm]

theorem expression_identity (lam S p : ℝ) : numerator lam S p=ExtendedScalarExpressions.binaryGap lam S p := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,ExtendedScalarExpressions.binaryGap,Variational.quadratic] <;> ring
end OptimalG.Certificates.ExtendedCoefficientData.BinaryGap
