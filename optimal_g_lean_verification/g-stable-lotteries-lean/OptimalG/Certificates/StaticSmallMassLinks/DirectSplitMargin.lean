import OptimalG.Certificates.SmallMassExpressions
import OptimalG.Certificates.StaticLowParameters
import OptimalG.Certificates.TensorBernstein

/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.DirectSplitMargin
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := ((-500 * (SmallMassExpressions.denominator lam S p)) + (-500 * (lam^2)) + (-500 * (p^2)) + (391 * lam) + (391 * p) + (-1000 * lam * p) + (500 * (SmallMassExpressions.initial lam S) * lam) + (500 * (SmallMassExpressions.initial lam S) * p))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := (500 * (SmallMassExpressions.denominator lam S p))


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (SmallMassExpressions.beta lam S p*(SmallMassExpressions.initial lam S-lam+391/500-p)-1)*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨48076414550032026621640663696807189534677083, 0, 2, 0, 0, 0, 0⟩,
  ⟨76072789232915736632189763583364764803754166, 1, 1, 0, 0, 0, 0⟩,
  ⟨27596578098172469851389645331620557437077083, 2, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (506457591003276164796022200000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((1/25)+(1/10)*x)=
      27596578098172469851389645331620557437077083+certificate.eval x 0 0 := by
  norm_num [semanticNumerator,certificate,TensorBernstein3.eval,TensorBernsteinTerm3.eval,
    SmallMassExpressions.denominator,smallMassDenominator,SmallMassExpressions.primitive,
    SmallMassExpressions.score,SmallMassExpressions.initial,SmallMassExpressions.slope,
    SmallMassExpressions.cap28,SmallMassExpressions.cap2918,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic,
    StaticLow.lam,StaticLow.slack]
  <;> ring

theorem numerator_positive {p : ℝ} (hp : p∈Icc ((1/25):ℝ) (7/50)) :
    0<semanticNumerator StaticLow.lam StaticLow.slack p := by
  have hx : (p-(1/25))/(1/10)∈Icc (0:ℝ) 1 := by
    convert! normalized_coordinate_mem (by norm_num : ((1/25):ℝ)<(7/50)) hp using 1 <;> norm_num
  have hh := TensorBernstein3.check_sound certificate_checked hx
    (by norm_num : (0:ℝ)∈Icc 0 1) (by norm_num : (0:ℝ)∈Icc 0 1)
  have he := certificate_identity ((p-(1/25))/(1/10))
  rw [show ((1/25):ℝ)+(1/10)*((p-(1/25))/(1/10))=p by ring] at he
  have hm : (0:ℝ)<27596578098172469851389645331620557437077083 := by norm_num
  have hs : (0:ℝ)<506457591003276164796022200000000000000000 := by norm_num
  have hprod : 0<(506457591003276164796022200000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((1/25):ℝ) (7/50))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*(SmallMassExpressions.initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)-(StaticLow.lam:ℝ)+391/500-p)-1) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*(SmallMassExpressions.initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)-(StaticLow.lam:ℝ)+391/500-p)-1)*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.DirectSplitMargin
