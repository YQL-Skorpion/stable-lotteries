import OptimalG.Certificates.DenseBernstein
import OptimalG.Certificates.SmallMassExpressions

namespace OptimalG.Certificates.BinarySmallData.CentralAnchor
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numeratorPolynomial : RationalPolynomial3 := [[[0, (59/50), (-1/2)], [1]], [[0, (-1501187/555458)], [0, (-2374772000000/602596665441)]], [[0, (668000/277729)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-35215307486496079/7775440844400000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(13/20), (31/40)⟩]
def numeratorScale : ℚ := 241038666176400000000
def numeratorCertificate : DenseBernstein3 := [[[11507256410823802311, 14592132129111420622, 1201761138784493311], [11439725689715458951, 14414598491382589402, 1091758222164005451]], [[23014444584314647972, 29184114660992897819, 2403440917671999847], [22879381178327751292, 28829043080346698159, 2183432743012696867]], [[11507188182911808979, 14591982552535127548, 1201679790120193569], [11439655498033255659, 14414444609617759108, 1091674532081378449]]]
noncomputable def numerator (lam S p : ℝ) : ℝ := numeratorPolynomial.eval lam S p

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {lam S p : ℝ}
    (hlam : lam∈Icc (22493/40000) (56233/100000))
    (hS : S∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (31/40))
    : 0<numerator lam S p := by
  have hx : ∀ i,(numeratorBox i).Contains (![lam, S, p] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hlam
    · simpa [numeratorBox,RatInterval.Contains] using hS
    · simpa [numeratorBox,RatInterval.Contains] using hp
  have hh := DenseBernstein3.scaledBoxCheck_sound numeratorChecked ![lam, S, p] hx
  have he : numeratorReduced.eval lam S p=numerator lam S p-(35215307486496079/7775440844400000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval lam S p at hh
  rw [he] at hh
  have hm : (0:ℝ)<(35215307486496079/7775440844400000000) := by norm_num
  linarith only [hh,hm]

theorem expression_identity (lam S p : ℝ) : numerator lam S p=-(Variational.quadratic lam p-S+p*(lam-9/50-1+p-SmallMassExpressions.initial lam S-SmallMassExpressions.slope lam S*(9/50))) := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,
    SmallMassExpressions.initial,SmallMassExpressions.slope,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic]
  <;> ring

end OptimalG.Certificates.BinarySmallData.CentralAnchor
