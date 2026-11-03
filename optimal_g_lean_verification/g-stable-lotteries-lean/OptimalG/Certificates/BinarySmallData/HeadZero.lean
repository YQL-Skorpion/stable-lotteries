import OptimalG.Certificates.DenseBernstein
import OptimalG.Certificates.SmallMassExpressions

namespace OptimalG.Certificates.BinarySmallData.HeadZero
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numeratorPolynomial : RationalPolynomial3 := [[[(1/2), -1, (1/2)], [1]], [[-1, 1]], [[(-3473/1054), (2000000/277729)], [(-9676000000/1143447183), (7568000000000/602596665441)]], [[(4000/527), (-4000000/277729)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-1869564476363771/49681344000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨0, (527/2000)⟩]
def numeratorScale : ℚ := 9147577464000000000000
def numeratorCertificate : DenseBernstein3 := [[[1551998614024680810625, 1582325929409248540000, 347895758071974729375], [1542247480777249828625, 1568912597300322164000, 344233559210479335375]], [[4656100042720440772775, 4747135054790963893250, 1043740340132744120475], [4626846366093654477175, 4706894612976608032450, 1032753574945174555275]], [[4656204245497551415715, 4747292324602634045390, 1043793407167303629675], [4626950291985040789795, 4707051437298720890830, 1032806473375901101035]], [[1552102816801800132481, 1582483199220931710514, 347948825106538578033], [1542351406668644820161, 1569069421622448040754, 344286457641210220593]]]
noncomputable def numerator (lam S p : ℝ) : ℝ := numeratorPolynomial.eval lam S p

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {lam S p : ℝ}
    (hlam : lam∈Icc (22493/40000) (56233/100000))
    (hS : S∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc 0 (527/2000))
    : 0<numerator lam S p := by
  have hx : ∀ i,(numeratorBox i).Contains (![lam, S, p] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hlam
    · simpa [numeratorBox,RatInterval.Contains] using hS
    · simpa [numeratorBox,RatInterval.Contains] using hp
  have hh := DenseBernstein3.scaledBoxCheck_sound numeratorChecked ![lam, S, p] hx
  have he : numeratorReduced.eval lam S p=numerator lam S p-(1869564476363771/49681344000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval lam S p at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1869564476363771/49681344000000000) := by norm_num
  linarith only [hh,hm]

theorem expression_identity (lam S p : ℝ) : numerator lam S p=lam*(SmallMassExpressions.initial lam S+SmallMassExpressions.slope lam S*p/2)-(Variational.quadratic lam (1-p)-S) := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,
    SmallMassExpressions.initial,SmallMassExpressions.slope,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic]
  <;> ring

end OptimalG.Certificates.BinarySmallData.HeadZero
