import OptimalG.Certificates.SmallMassExpressions
import OptimalG.Certificates.StaticLowParameters
import OptimalG.Certificates.TensorBernstein

/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.CapRateRight
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := ((1000 * ((SmallMassExpressions.denominator lam S p)^2)) + (-1000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.primitive lam S p)) + (-1000 * (SmallMassExpressions.cap28 lam S) * (p^2)) + (-1000 * (SmallMassExpressions.primitive lam S p) * (lam^2)) + (-1000 * (SmallMassExpressions.primitive lam S p) * (p^2)) + (-500 * (SmallMassExpressions.cap28 lam S) * (p^4)) + (-109 * (SmallMassExpressions.cap28 lam S) * (lam^2)) + (109 * (SmallMassExpressions.cap28 lam S) * (lam^3)) + (1000 * lam * (SmallMassExpressions.primitive lam S p)) + (1000 * (SmallMassExpressions.primitive lam S p) * p) + (1500 * (SmallMassExpressions.cap28 lam S) * (p^3)) + (-2500 * (SmallMassExpressions.cap28 lam S) * (lam^2) * (p^2)) + (-2000 * lam * (SmallMassExpressions.cap28 lam S) * (p^3)) + (-2000 * lam * (SmallMassExpressions.primitive lam S p) * p) + (-1500 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap28 lam S) * (p^2)) + (-1109 * lam * (SmallMassExpressions.cap28 lam S) * p) + (-1000 * (SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.score lam S p)) + (-1000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap28 lam S) * (lam^2)) + (-1000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.score lam S p) * p) + (-1000 * (SmallMassExpressions.cap28 lam S) * (SmallMassExpressions.score lam S p) * (p^2)) + (-1000 * (SmallMassExpressions.cap28 lam S) * p * (lam^3)) + (-109 * (SmallMassExpressions.cap28 lam S) * (SmallMassExpressions.score lam S p) * (lam^2)) + (500 * (SmallMassExpressions.cap28 lam S) * (SmallMassExpressions.score lam S p) * (p^3)) + (1000 * lam * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p)) + (1000 * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p) * p) + (1109 * (SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.cap28 lam S)) + (2000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap28 lam S) * p) + (2218 * (SmallMassExpressions.cap28 lam S) * p * (lam^2)) + (3609 * lam * (SmallMassExpressions.cap28 lam S) * (p^2)) + (-3000 * (SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.cap28 lam S) * p) + (-1109 * lam * (SmallMassExpressions.cap28 lam S) * (SmallMassExpressions.score lam S p) * p) + (1000 * (SmallMassExpressions.cap28 lam S) * (SmallMassExpressions.score lam S p) * p * (lam^2)) + (1500 * lam * (SmallMassExpressions.cap28 lam S) * (SmallMassExpressions.score lam S p) * (p^2)))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := (1000 * (SmallMassExpressions.cap28 lam S) * ((SmallMassExpressions.denominator lam S p)^2))


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (SmallMassExpressions.rateRight lam S p (SmallMassExpressions.cap28 lam S))*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨5949334677172899893292017400367184651888761960931771944839169057587578013522798325176, 0, 4, 0, 0, 0, 0⟩,
  ⟨33415594084288022202143932526369247114523962312630520793381294375089100187939924916368, 1, 3, 0, 0, 0, 0⟩,
  ⟨63867222393794290106312302451588376310074264196321839707296843148033819963057682574500, 2, 2, 0, 0, 0, 0⟩,
  ⟨51055727106500691705415688168707589801073489814745846526891841768387316673450632970600, 3, 1, 0, 0, 0, 0⟩,
  ⟨14666149970877934103030842332861884102217279697128544267480818018736714094431547897292, 4, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (1323962514214353203403923685617095283959296000000000000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((1/5)+(127/2000)*x)=
      5949334677172899893292017400367184651888761960931771944839169057587578013522798325176+certificate.eval x 0 0 := by
  norm_num [semanticNumerator,certificate,TensorBernstein3.eval,TensorBernsteinTerm3.eval,
    SmallMassExpressions.denominator,smallMassDenominator,SmallMassExpressions.primitive,
    SmallMassExpressions.score,SmallMassExpressions.initial,SmallMassExpressions.slope,
    SmallMassExpressions.cap28,SmallMassExpressions.cap2918,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic,
    StaticLow.lam,StaticLow.slack]
  <;> ring

theorem numerator_positive {p : ℝ} (hp : p∈Icc ((1/5):ℝ) (527/2000)) :
    0<semanticNumerator StaticLow.lam StaticLow.slack p := by
  have hx : (p-(1/5))/(127/2000)∈Icc (0:ℝ) 1 := by
    convert! normalized_coordinate_mem (by norm_num : ((1/5):ℝ)<(527/2000)) hp using 1 <;> norm_num
  have hh := TensorBernstein3.check_sound certificate_checked hx
    (by norm_num : (0:ℝ)∈Icc 0 1) (by norm_num : (0:ℝ)∈Icc 0 1)
  have he := certificate_identity ((p-(1/5))/(127/2000))
  rw [show ((1/5):ℝ)+(127/2000)*((p-(1/5))/(127/2000))=p by ring] at he
  have hm : (0:ℝ)<5949334677172899893292017400367184651888761960931771944839169057587578013522798325176 := by norm_num
  have hs : (0:ℝ)<1323962514214353203403923685617095283959296000000000000000000000000000000000000000000 := by norm_num
  have hprod : 0<(1323962514214353203403923685617095283959296000000000000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((1/5):ℝ) (527/2000))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(SmallMassExpressions.rateRight (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (SmallMassExpressions.cap28 (StaticLow.lam:ℝ) (StaticLow.slack:ℝ))) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(SmallMassExpressions.rateRight (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (SmallMassExpressions.cap28 (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)))*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.CapRateRight
