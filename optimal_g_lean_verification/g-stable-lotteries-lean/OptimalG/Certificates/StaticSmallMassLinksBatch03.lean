import OptimalG.Certificates.SmallMassExpressions
import OptimalG.Certificates.StaticLowParameters
import OptimalG.Certificates.TensorBernstein


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.DirectEndpointOne1
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := ((-298987 * lam) + (-298987 * p) + (2743000 * (SmallMassExpressions.denominator lam S p)) + (2743000 * (p^2)) + (25000000 * (p^3)) + (2743000 * lam * p) + (25000000 * lam * (p^2)))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := (50000000 * (SmallMassExpressions.denominator lam S p))


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (-(1-lam)*(1+SmallMassExpressions.beta lam S p*p-SmallMassExpressions.etaOne lam S p)+SmallMassExpressions.beta lam S p*p^2/2-(SmallMassExpressions.beta lam S p*(109/1000)-SmallMassExpressions.etaOne lam S p)*(13/50)*(211/1000))*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨83726140103879345343707488672819754965301667, 0, 3, 0, 0, 0, 0⟩,
  ⟨999257300190180314241898696846953198955820961, 1, 2, 0, 0, 0, 0⟩,
  ⟨2013094438311849252136073601535100572494792921, 2, 1, 0, 0, 0, 0⟩,
  ⟨1135547597550793995597584058360967128504273627, 3, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (1519372773009828494388066600000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((1/25)+(1/10)*x)=
      83726140103879345343707488672819754965301667+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<83726140103879345343707488672819754965301667 := by norm_num
  have hs : (0:ℝ)<1519372773009828494388066600000000000000 := by norm_num
  have hprod : 0<(1519372773009828494388066600000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((1/25):ℝ) (7/50))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(-(1-(StaticLow.lam:ℝ))*(1+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p-SmallMassExpressions.etaOne (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p^2/2-(SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*(109/1000)-SmallMassExpressions.etaOne (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)*(13/50)*(211/1000)) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(-(1-(StaticLow.lam:ℝ))*(1+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p-SmallMassExpressions.etaOne (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p^2/2-(SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*(109/1000)-SmallMassExpressions.etaOne (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)*(13/50)*(211/1000))*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.DirectEndpointOne1


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.DirectEndpointOne2
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := ((-52743000 * (SmallMassExpressions.denominator lam S p) * p) + (-50000000 * (SmallMassExpressions.cap28 lam S) * (p^2)) + (-50000000 * (SmallMassExpressions.primitive lam S p) * (lam^2)) + (-298987 * lam * (SmallMassExpressions.cap28 lam S)) + (-298987 * (SmallMassExpressions.cap28 lam S) * p) + (2743000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap28 lam S)) + (25000000 * (SmallMassExpressions.cap28 lam S) * (p^3)) + (52743000 * lam * (SmallMassExpressions.primitive lam S p)) + (52743000 * (SmallMassExpressions.primitive lam S p) * p) + (-50000000 * lam * (SmallMassExpressions.cap28 lam S) * p) + (-50000000 * lam * (SmallMassExpressions.primitive lam S p) * p) + (50000000 * (SmallMassExpressions.denominator lam S p) * lam * p) + (50000000 * (SmallMassExpressions.cap28 lam S) * p * (lam^2)) + (75000000 * lam * (SmallMassExpressions.cap28 lam S) * (p^2)))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := (50000000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap28 lam S))


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (-(1-lam)*(1+SmallMassExpressions.beta lam S p*p-SmallMassExpressions.etaTwo lam S p)+SmallMassExpressions.beta lam S p*p^2/2-(SmallMassExpressions.beta lam S p*(109/1000)-SmallMassExpressions.etaTwo lam S p)*(13/50)*(211/1000))*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨277821552902751138097994817951421568296708256256752919040844706180614355363549, 0, 3, 0, 0, 0, 0⟩,
  ⟨1574153027400095533075723512916278079354538476171740241853758016292645171021567, 1, 2, 0, 0, 0, 0⟩,
  ⟨1264520957311291852756761456004350149586966911196763210085696601168179130464487, 2, 1, 0, 0, 0, 0⟩,
  ⟨92096922440337898123031470921160467341653113797965439517738291056148314806469, 3, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (6619812571071766017019618428085476419796480000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((1/25)+(1/10)*x)=
      92096922440337898123031470921160467341653113797965439517738291056148314806469+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<92096922440337898123031470921160467341653113797965439517738291056148314806469 := by norm_num
  have hs : (0:ℝ)<6619812571071766017019618428085476419796480000000000000000000000000000000 := by norm_num
  have hprod : 0<(6619812571071766017019618428085476419796480000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((1/25):ℝ) (7/50))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(-(1-(StaticLow.lam:ℝ))*(1+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p-SmallMassExpressions.etaTwo (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p^2/2-(SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*(109/1000)-SmallMassExpressions.etaTwo (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)*(13/50)*(211/1000)) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(-(1-(StaticLow.lam:ℝ))*(1+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p-SmallMassExpressions.etaTwo (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p^2/2-(SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*(109/1000)-SmallMassExpressions.etaTwo (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)*(13/50)*(211/1000))*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.DirectEndpointOne2


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.DirectEndpointSwitch1
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := ((p^3) + (lam * (p^2)))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := (2 * (SmallMassExpressions.denominator lam S p))


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (-(789/1000-lam)*(1+SmallMassExpressions.beta lam S p*p-SmallMassExpressions.etaOne lam S p)+SmallMassExpressions.beta lam S p*p^2/2)*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨722796, 0, 3, 0, 0, 0, 0⟩,
  ⟨9636348, 1, 2, 0, 0, 0, 0⟩,
  ⟨27339258, 2, 1, 0, 0, 0, 0⟩,
  ⟨19925706, 3, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (1500000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((1/25)+(1/10)*x)=
      722796+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<722796 := by norm_num
  have hs : (0:ℝ)<1500000000 := by norm_num
  have hprod : 0<(1500000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((1/25):ℝ) (7/50))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(-(789/1000-(StaticLow.lam:ℝ))*(1+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p-SmallMassExpressions.etaOne (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p^2/2) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(-(789/1000-(StaticLow.lam:ℝ))*(1+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p-SmallMassExpressions.etaOne (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p^2/2)*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.DirectEndpointSwitch1


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.DirectEndpointSwitch2
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := ((-1000 * (SmallMassExpressions.primitive lam S p) * (lam^2)) + (-789 * (SmallMassExpressions.denominator lam S p) * p) + (-789 * (SmallMassExpressions.cap28 lam S) * (p^2)) + (500 * (SmallMassExpressions.cap28 lam S) * (p^3)) + (789 * lam * (SmallMassExpressions.primitive lam S p)) + (789 * (SmallMassExpressions.primitive lam S p) * p) + (-1000 * lam * (SmallMassExpressions.primitive lam S p) * p) + (-789 * lam * (SmallMassExpressions.cap28 lam S) * p) + (1000 * (SmallMassExpressions.denominator lam S p) * lam * p) + (1000 * (SmallMassExpressions.cap28 lam S) * p * (lam^2)) + (1500 * lam * (SmallMassExpressions.cap28 lam S) * (p^2)))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := (1000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap28 lam S))


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (-(789/1000-lam)*(1+SmallMassExpressions.beta lam S p*p-SmallMassExpressions.etaTwo lam S p)+SmallMassExpressions.beta lam S p*p^2/2)*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨275106743754621291470115507727940470198132486971225177, 0, 3, 0, 0, 0, 0⟩,
  ⟨1268694570676086423223142442119056563686038703085274941, 1, 2, 0, 0, 0, 0⟩,
  ⟨837931277932437834069586003377547093445992637724624351, 2, 1, 0, 0, 0, 0⟩,
  ⟨55627171250539377330512240020620883305850906110574587, 3, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (875158717253661212767526361600000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((1/25)+(1/10)*x)=
      55627171250539377330512240020620883305850906110574587+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<55627171250539377330512240020620883305850906110574587 := by norm_num
  have hs : (0:ℝ)<875158717253661212767526361600000000000000000000000000 := by norm_num
  have hprod : 0<(875158717253661212767526361600000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((1/25):ℝ) (7/50))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(-(789/1000-(StaticLow.lam:ℝ))*(1+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p-SmallMassExpressions.etaTwo (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p^2/2) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(-(789/1000-(StaticLow.lam:ℝ))*(1+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p-SmallMassExpressions.etaTwo (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p^2/2)*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.DirectEndpointSwitch2
