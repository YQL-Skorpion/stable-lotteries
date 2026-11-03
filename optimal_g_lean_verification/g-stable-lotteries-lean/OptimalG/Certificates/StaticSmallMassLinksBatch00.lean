import OptimalG.Certificates.SmallMassExpressions
import OptimalG.Certificates.StaticLowParameters
import OptimalG.Certificates.TensorBernstein


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.CapBetaDerivative
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := (lam + p + (-1 * (SmallMassExpressions.denominator lam S p)) + (-1 * (lam^2)) + (-1 * (p^2)) + (lam * (SmallMassExpressions.score lam S p)) + ((SmallMassExpressions.score lam S p) * p) + (-2 * lam * p))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := ((SmallMassExpressions.denominator lam S p)^2)


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (-SmallMassExpressions.betaDerivative lam S p)*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨39846550125042079318165620293601677113588827, 0, 2, 0, 0, 0, 0⟩,
  ⟨59047190991760241522069556534589591636308366, 1, 1, 0, 0, 0, 0⟩,
  ⟨18340767033926871859331627045927393538027739, 2, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (253228795501638082398011100000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((1/5)+(127/2000)*x)=
      18340767033926871859331627045927393538027739+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<18340767033926871859331627045927393538027739 := by norm_num
  have hs : (0:ℝ)<253228795501638082398011100000000000000000000 := by norm_num
  have hprod : 0<(253228795501638082398011100000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((1/5):ℝ) (527/2000))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(-SmallMassExpressions.betaDerivative (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(-SmallMassExpressions.betaDerivative (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.CapBetaDerivative


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.CapMinimizerHeadZero
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := ((1459 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S)) + (-5000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S) * lam) + (-5000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap2918 lam S) * p) + (-5000 * (SmallMassExpressions.initial lam S) * lam * (SmallMassExpressions.primitive lam S p)) + (-5000 * (SmallMassExpressions.initial lam S) * (SmallMassExpressions.primitive lam S p) * p) + (5000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S) * p) + (5000 * (SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.cap2918 lam S)) + (5000 * lam * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.cap2918 lam S)) + (5000 * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.cap2918 lam S) * p))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := (5000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap2918 lam S))


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (SmallMassExpressions.target lam S p-SmallMassExpressions.etaWitness lam S p*SmallMassExpressions.initial lam S)*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨4479853398708821388437453544589495432232229594932040010545893598813051334523209430135625, 0, 3, 0, 0, 0, 0⟩,
  ⟨20468217257721360003844925164998311730943562157520298333493373253629638662989657527411237, 1, 2, 0, 0, 0, 0⟩,
  ⟨29093314956997598734407350381786948100251915010440679663220647501732278687094330874732491, 2, 1, 0, 0, 0, 0⟩,
  ⟨12867638353616131187851149465930444798907661224891301277212573322013729703146632777456879, 3, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (2034258565878840695636614708652579903709328455233736840000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((1/5)+(127/2000)*x)=
      4479853398708821388437453544589495432232229594932040010545893598813051334523209430135625+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<4479853398708821388437453544589495432232229594932040010545893598813051334523209430135625 := by norm_num
  have hs : (0:ℝ)<2034258565878840695636614708652579903709328455233736840000000000000000000000000000000000 := by norm_num
  have hprod : 0<(2034258565878840695636614708652579903709328455233736840000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((1/5):ℝ) (527/2000))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(SmallMassExpressions.target (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p-SmallMassExpressions.etaWitness (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*SmallMassExpressions.initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(SmallMassExpressions.target (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p-SmallMassExpressions.etaWitness (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*SmallMassExpressions.initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ))*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.CapMinimizerHeadZero


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.CapMinimizerTwo
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := ((1459 * (SmallMassExpressions.denominator lam S p)) + (-5000 * (SmallMassExpressions.denominator lam S p) * lam) + (-5000 * lam * (SmallMassExpressions.primitive lam S p)) + (-5000 * (SmallMassExpressions.primitive lam S p) * p) + (5000 * (SmallMassExpressions.denominator lam S p) * p) + (10000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap2918 lam S)))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := (5000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap2918 lam S))


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (2-SmallMassExpressions.etaWitness lam S p)*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨123993966004062007693941577370026591204733355140798829898930080514046412450, 0, 3, 0, 0, 0, 0⟩,
  ⟨449622767782166087823820645058765703530768591817196425988661481832850192508, 1, 2, 0, 0, 0, 0⟩,
  ⟨532765409822921208477348158800783341224023268639506192751398800699743894094, 2, 1, 0, 0, 0, 0⟩,
  ⟨205770036180184292042039292431930893402685635904891281661667399380940114036, 3, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (2134869292913032463838723410789229155371660176000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((1/5)+(127/2000)*x)=
      123993966004062007693941577370026591204733355140798829898930080514046412450+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<123993966004062007693941577370026591204733355140798829898930080514046412450 := by norm_num
  have hs : (0:ℝ)<2134869292913032463838723410789229155371660176000000000000000000000000000 := by norm_num
  have hprod : 0<(2134869292913032463838723410789229155371660176000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((1/5):ℝ) (527/2000))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(2-SmallMassExpressions.etaWitness (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(2-SmallMassExpressions.etaWitness (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.CapMinimizerTwo


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.CapRateLeft
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := ((391 * ((SmallMassExpressions.denominator lam S p)^2)) + (-891 * (SmallMassExpressions.primitive lam S p) * (lam^2)) + (-500 * lam * ((SmallMassExpressions.denominator lam S p)^2)) + (-391 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.primitive lam S p)) + (-391 * (SmallMassExpressions.cap28 lam S) * (p^2)) + (-391 * (SmallMassExpressions.primitive lam S p) * (p^2)) + (-250 * (SmallMassExpressions.cap28 lam S) * (p^4)) + (391 * lam * (SmallMassExpressions.primitive lam S p)) + (391 * (SmallMassExpressions.primitive lam S p) * p) + (500 * (SmallMassExpressions.primitive lam S p) * (lam^3)) + (641 * (SmallMassExpressions.cap28 lam S) * (p^3)) + (-1282 * lam * (SmallMassExpressions.primitive lam S p) * p) + (-1250 * (SmallMassExpressions.cap28 lam S) * (lam^2) * (p^2)) + (-1000 * lam * (SmallMassExpressions.cap28 lam S) * (p^3)) + (-750 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap28 lam S) * (p^2)) + (-500 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap28 lam S) * (lam^2)) + (-500 * (SmallMassExpressions.cap28 lam S) * p * (lam^3)) + (-500 * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p) * (lam^2)) + (-391 * (SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.score lam S p)) + (-391 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.score lam S p) * p) + (-391 * lam * (SmallMassExpressions.cap28 lam S) * p) + (-391 * (SmallMassExpressions.cap28 lam S) * (SmallMassExpressions.score lam S p) * (p^2)) + (250 * (SmallMassExpressions.cap28 lam S) * (SmallMassExpressions.score lam S p) * (p^3)) + (391 * (SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.cap28 lam S)) + (391 * lam * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p)) + (391 * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p) * p) + (500 * (SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.primitive lam S p)) + (500 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.score lam S p) * (lam^2)) + (500 * lam * (SmallMassExpressions.primitive lam S p) * (p^2)) + (782 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap28 lam S) * p) + (891 * (SmallMassExpressions.cap28 lam S) * p * (lam^2)) + (1000 * (SmallMassExpressions.primitive lam S p) * p * (lam^2)) + (1532 * lam * (SmallMassExpressions.cap28 lam S) * (p^2)) + (-1500 * (SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.cap28 lam S) * p) + (-500 * lam * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p) * p) + (-391 * lam * (SmallMassExpressions.cap28 lam S) * (SmallMassExpressions.score lam S p) * p) + (500 * (SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.score lam S p) * p) + (500 * (SmallMassExpressions.cap28 lam S) * (SmallMassExpressions.score lam S p) * p * (lam^2)) + (750 * lam * (SmallMassExpressions.cap28 lam S) * (SmallMassExpressions.score lam S p) * (p^2)))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := (500 * (SmallMassExpressions.cap28 lam S) * ((SmallMassExpressions.denominator lam S p)^2))


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (SmallMassExpressions.rateLeft lam S p (SmallMassExpressions.cap28 lam S))*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨468033997049100830501415774849677557312198290704034914696640677990344545143441106958, 0, 4, 0, 0, 0, 0⟩,
  ⟨1680249294782666035256122960797592503676775301682652829946841671009495640340441411432, 1, 3, 0, 0, 0, 0⟩,
  ⟨1993905244794255840730869083996974205753476192247672389008092848600616796966061987632, 2, 2, 0, 0, 0, 0⟩,
  ⟨790248491117825336612011060738333043173946596362402236391118580398933272505847258800, 3, 1, 0, 0, 0, 0⟩,
  ⟨9996218439023697864254375590834211889020413405365383087625908966725973943942545642, 4, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (882641676142902135602615790411396855972864000000000000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((1/5)+(127/2000)*x)=
      9996218439023697864254375590834211889020413405365383087625908966725973943942545642+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<9996218439023697864254375590834211889020413405365383087625908966725973943942545642 := by norm_num
  have hs : (0:ℝ)<882641676142902135602615790411396855972864000000000000000000000000000000000000000000 := by norm_num
  have hprod : 0<(882641676142902135602615790411396855972864000000000000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((1/5):ℝ) (527/2000))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(SmallMassExpressions.rateLeft (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (SmallMassExpressions.cap28 (StaticLow.lam:ℝ) (StaticLow.slack:ℝ))) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(SmallMassExpressions.rateLeft (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (SmallMassExpressions.cap28 (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)))*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.CapRateLeft
