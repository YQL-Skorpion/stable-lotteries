import OptimalG.Certificates.SmallMassExpressions
import OptimalG.Certificates.StaticLowParameters
import OptimalG.Certificates.TensorBernstein


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.HeadRateSlope
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := (((SmallMassExpressions.denominator lam S p)^2) + ((SmallMassExpressions.initial lam S) * (p^3)) + (lam * (SmallMassExpressions.primitive lam S p)) + ((SmallMassExpressions.primitive lam S p) * p) + (-1 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.primitive lam S p)) + (-1 * (SmallMassExpressions.initial lam S) * (p^2)) + (-1 * (SmallMassExpressions.primitive lam S p) * (lam^2)) + (-1 * (SmallMassExpressions.primitive lam S p) * (p^2)) + ((SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S) * lam) + ((SmallMassExpressions.initial lam S) * p * (lam^2)) + (lam * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p)) + ((SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p) * p) + (-1 * (SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.score lam S p)) + (-1 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.score lam S p) * p) + (-1 * (SmallMassExpressions.initial lam S) * lam * p) + (-1 * (SmallMassExpressions.initial lam S) * (SmallMassExpressions.score lam S p) * (p^2)) + (-2 * lam * (SmallMassExpressions.primitive lam S p) * p) + (2 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S) * p) + (2 * (SmallMassExpressions.initial lam S) * lam * (p^2)) + (-1 * (SmallMassExpressions.initial lam S) * lam * (SmallMassExpressions.score lam S p) * p))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := ((SmallMassExpressions.initial lam S) * ((SmallMassExpressions.denominator lam S p)^2))


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (SmallMassExpressions.rateSlope lam S p (SmallMassExpressions.initial lam S))*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨87788347739493113794923172918623242207489394870210265983327086779625236919090311, 0, 4, 0, 0, 0, 0⟩,
  ⟨457549732411738750741289214447821909980136942125200597986082375490326767827606780, 1, 3, 0, 0, 0, 0⟩,
  ⟨858852590580853896296249096676827508042555175098752044134166184117271346110198666, 2, 2, 0, 0, 0, 0⟩,
  ⟨695369042719762554234219530699773357836606670492587071300880210154063336413938236, 3, 1, 0, 0, 0, 0⟩,
  ⟨206311036557576094264375674891500928207669341204687646561587152507493521212256039, 4, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (6083949039014273198781678198406335274746986311500000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((7/50)+(3/50)*x)=
      87788347739493113794923172918623242207489394870210265983327086779625236919090311+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<87788347739493113794923172918623242207489394870210265983327086779625236919090311 := by norm_num
  have hs : (0:ℝ)<6083949039014273198781678198406335274746986311500000000000000000000000000000000000 := by norm_num
  have hprod : 0<(6083949039014273198781678198406335274746986311500000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((7/50):ℝ) (1/5))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(SmallMassExpressions.rateSlope (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (SmallMassExpressions.initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ))) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(SmallMassExpressions.rateSlope (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (SmallMassExpressions.initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)))*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.HeadRateSlope


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.HeadSplitMargin
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
  ⟨33932431394391732158861489027546315625717083, 0, 2, 0, 0, 0, 0⟩,
  ⟨55337082966840986160076694303018441293674166, 1, 1, 0, 0, 0, 0⟩,
  ⟨21260724801953207543917801635694799248437083, 2, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (506457591003276164796022200000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((7/50)+(3/50)*x)=
      21260724801953207543917801635694799248437083+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<21260724801953207543917801635694799248437083 := by norm_num
  have hs : (0:ℝ)<506457591003276164796022200000000000000000 := by norm_num
  have hprod : 0<(506457591003276164796022200000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((7/50):ℝ) (1/5))
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

end OptimalG.Certificates.StaticSmallMassLinks.HeadSplitMargin


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.HeadSupportWitness
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := ((1459 * (SmallMassExpressions.denominator lam S p)) + (-5000 * (SmallMassExpressions.denominator lam S p) * lam) + (-5000 * lam * (SmallMassExpressions.primitive lam S p)) + (-5000 * (SmallMassExpressions.primitive lam S p) * p) + (5000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap2918 lam S)) + (5000 * (SmallMassExpressions.denominator lam S p) * p) + (5000 * (SmallMassExpressions.cap2918 lam S) * (p^2)) + (5000 * lam * (SmallMassExpressions.cap2918 lam S) * p))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := (5000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap2918 lam S))


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (1+SmallMassExpressions.beta lam S p*p-SmallMassExpressions.etaWitness lam S p)*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨1753263995890386468412632491466844038954766274476964995512460212048370187, 0, 3, 0, 0, 0, 0⟩,
  ⟨11476818544395400894569149967689178452373445641457685778310068361904979657, 1, 2, 0, 0, 0, 0⟩,
  ⟨19456869444164512868752644404058967313019946785344561402686844872078000113, 2, 1, 0, 0, 0, 0⟩,
  ⟨9656459601114629273897932885048220650007887652027840619889236722221390643, 3, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (142324619527535497589248227385948610358110678400000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((7/50)+(3/50)*x)=
      1753263995890386468412632491466844038954766274476964995512460212048370187+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<1753263995890386468412632491466844038954766274476964995512460212048370187 := by norm_num
  have hs : (0:ℝ)<142324619527535497589248227385948610358110678400000000000000000000000000 := by norm_num
  have hprod : 0<(142324619527535497589248227385948610358110678400000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((7/50):ℝ) (1/5))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(1+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p-SmallMassExpressions.etaWitness (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(1+SmallMassExpressions.beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p-SmallMassExpressions.etaWitness (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.HeadSupportWitness


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.HeadTarget
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := ((lam * (SmallMassExpressions.primitive lam S p)) + ((SmallMassExpressions.primitive lam S p) * p) + (-1 * (SmallMassExpressions.denominator lam S p) * p))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := (SmallMassExpressions.denominator lam S p)


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (SmallMassExpressions.target lam S p-lam)*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨113768786805766023265249834536067538023019021, 0, 3, 0, 0, 0, 0⟩,
  ⟨386702173425297072027216920008069585491038601, 1, 2, 0, 0, 0, 0⟩,
  ⟨412951402127314482017028229793405755187454219, 2, 1, 0, 0, 0, 0⟩,
  ⟨141385451003492278900010404261403707719434639, 3, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (12661439775081904119900555000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((7/50)+(3/50)*x)=
      113768786805766023265249834536067538023019021+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<113768786805766023265249834536067538023019021 := by norm_num
  have hs : (0:ℝ)<12661439775081904119900555000000000000000000000 := by norm_num
  have hprod : 0<(12661439775081904119900555000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((7/50):ℝ) (1/5))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(SmallMassExpressions.target (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p-(StaticLow.lam:ℝ)) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(SmallMassExpressions.target (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p-(StaticLow.lam:ℝ))*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.HeadTarget
