import OptimalG.Certificates.SmallMassExpressions
import OptimalG.Certificates.StaticLowParameters
import OptimalG.Certificates.TensorBernstein


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.HeadTargetDerivative
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := (((SmallMassExpressions.denominator lam S p)^2) + (lam * (SmallMassExpressions.primitive lam S p)) + ((SmallMassExpressions.primitive lam S p) * p) + (-1 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.primitive lam S p)) + (-1 * (SmallMassExpressions.primitive lam S p) * (lam^2)) + (-1 * (SmallMassExpressions.primitive lam S p) * (p^2)) + (lam * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p)) + ((SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p) * p) + (-1 * (SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.score lam S p)) + (-1 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.score lam S p) * p) + (-2 * lam * (SmallMassExpressions.primitive lam S p) * p))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := ((SmallMassExpressions.denominator lam S p)^2)


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (-SmallMassExpressions.targetDerivative lam S p)*semanticDenominator lam S p=semanticNumerator lam S p := by
  dsimp only [semanticNumerator,semanticDenominator,
    SmallMassExpressions.beta,SmallMassExpressions.target,
    SmallMassExpressions.betaDerivative,SmallMassExpressions.targetDerivative,
    SmallMassExpressions.etaOne,SmallMassExpressions.etaTwo,
    SmallMassExpressions.etaWitness,SmallMassExpressions.rateSlope,
    SmallMassExpressions.rateLeft,SmallMassExpressions.rateRight,
    smallMassBeta,smallMassTarget,smallMassBetaDerivative,smallMassTargetDerivative]
  dsimp only [SmallMassExpressions.denominator] at hD ⊢
  field_simp [hD,hF,hM,hW]
  <;> ring


def certificate : TensorBernstein3 := [
  ⟨29877798403719986061144265749247176641412497633940234647272431090678863, 0, 4, 0, 0, 0, 0⟩,
  ⟨236762772934475080958893751278422015723608606018507616597930233806699772, 1, 3, 0, 0, 0, 0⟩,
  ⟨531044532681129791777880022151325859714977882115014600984816001801146138, 2, 2, 0, 0, 0, 0⟩,
  ⟨468372295292184356613521703665488925142918243549206656300931026544908412, 3, 1, 0, 0, 0, 0⟩,
  ⟨144328876293369577057667611001681752705074210308561448146772827459783183, 4, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (21282833626130934982701962538855055362000000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((7/50)+(3/50)*x)=
      29877798403719986061144265749247176641412497633940234647272431090678863+certificate.eval x 0 0 := by
  norm_num [semanticNumerator,certificate,TensorBernstein3.eval,TensorBernsteinTerm3.eval,
    SmallMassExpressions.denominator,smallMassDenominator,SmallMassExpressions.primitive,
    SmallMassExpressions.score,SmallMassExpressions.initial,SmallMassExpressions.slope,
    SmallMassExpressions.cap28,SmallMassExpressions.cap2918,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic,
    StaticLow.lam,StaticLow.slack]
  <;> ring

theorem numerator_positive {p : ℝ} (hp : p∈Icc ((7/50):ℝ) (1/5)) :
    0<semanticNumerator StaticLow.lam StaticLow.slack p := by
  have hx : (p-(7/50))/(3/50)∈Icc (0:ℝ) 1 := by
    convert! normalized_coordinate_mem (by norm_num : ((7/50):ℝ)<(1/5)) hp using 1 <;> norm_num
  have hh := TensorBernstein3.check_sound certificate_checked hx
    (by norm_num : (0:ℝ)∈Icc 0 1) (by norm_num : (0:ℝ)∈Icc 0 1)
  have he := certificate_identity ((p-(7/50))/(3/50))
  rw [show ((7/50):ℝ)+(3/50)*((p-(7/50))/(3/50))=p by ring] at he
  have hm : (0:ℝ)<29877798403719986061144265749247176641412497633940234647272431090678863 := by norm_num
  have hs : (0:ℝ)<21282833626130934982701962538855055362000000000000000000000000000000000000 := by norm_num
  have hprod : 0<(21282833626130934982701962538855055362000000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((7/50):ℝ) (1/5))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(-SmallMassExpressions.targetDerivative (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(-SmallMassExpressions.targetDerivative (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.HeadTargetDerivative
