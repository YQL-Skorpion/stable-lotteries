import OptimalG.Certificates.DenseBernstein
import OptimalG.Certificates.SmallMassExpressions

namespace OptimalG.Certificates.BinarySmallData.DerivativeMargin
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numeratorPolynomial : RationalPolynomial3 := [[[0, 1, (-1/2)], [1]], [[0, (-5581/1054)], [0, (-9676000000/1143447183)]], [[0, (4000/527)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-33182931953891/4573788732000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(43767/100000), (13/20)⟩]
def numeratorScale : ℚ := 1143447183000000000000
def numeratorCertificate : DenseBernstein3 := [[[65517126706894527850, 101110802372724272200, 9818072743831950000], [64729673007446834950, 98801008917917379300, 8295732988472750000]], [[131041882648993998275, 202240564441693111975, 19647475948703525000], [129466961781015319415, 197620944059559333115, 16602776434548425000]], [[65524756037061999568, 101129762304963753918, 9829403345903960000], [64737288868531013608, 98819935377636867958, 8307043587108060000]]]
noncomputable def numerator (lam S p : ℝ) : ℝ := numeratorPolynomial.eval lam S p

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {lam S p : ℝ}
    (hlam : lam∈Icc (22493/40000) (56233/100000))
    (hS : S∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (43767/100000) (13/20))
    : 0<numerator lam S p := by
  have hx : ∀ i,(numeratorBox i).Contains (![lam, S, p] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hlam
    · simpa [numeratorBox,RatInterval.Contains] using hS
    · simpa [numeratorBox,RatInterval.Contains] using hp
  have hh := DenseBernstein3.scaledBoxCheck_sound numeratorChecked ![lam, S, p] hx
  have he : numeratorReduced.eval lam S p=numerator lam S p-(33182931953891/4573788732000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval lam S p at hh
  rw [he] at hh
  have hm : (0:ℝ)<(33182931953891/4573788732000000) := by norm_num
  linarith only [hh,hm]

theorem expression_identity (lam S p : ℝ) : numerator lam S p=p*(1+SmallMassExpressions.initial lam S-2*lam)-p^2/2+S := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,
    SmallMassExpressions.initial,SmallMassExpressions.slope,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic]
  <;> ring

end OptimalG.Certificates.BinarySmallData.DerivativeMargin
