import OptimalG.Certificates.SmallMassExpressions
import OptimalG.Certificates.StaticLowParameters
import OptimalG.Certificates.TensorBernstein


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.CapRateSlope
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := (((SmallMassExpressions.denominator lam S p)^2) + (lam * (SmallMassExpressions.primitive lam S p)) + ((SmallMassExpressions.cap28 lam S) * (p^3)) + ((SmallMassExpressions.primitive lam S p) * p) + (-1 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.primitive lam S p)) + (-1 * (SmallMassExpressions.cap28 lam S) * (p^2)) + (-1 * (SmallMassExpressions.primitive lam S p) * (lam^2)) + (-1 * (SmallMassExpressions.primitive lam S p) * (p^2)) + ((SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.cap28 lam S)) + (lam * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p)) + ((SmallMassExpressions.cap28 lam S) * p * (lam^2)) + ((SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p) * p) + (-1 * (SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.score lam S p)) + (-1 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.score lam S p) * p) + (-1 * lam * (SmallMassExpressions.cap28 lam S) * p) + (-1 * (SmallMassExpressions.cap28 lam S) * (SmallMassExpressions.score lam S p) * (p^2)) + (-2 * lam * (SmallMassExpressions.primitive lam S p) * p) + (2 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap28 lam S) * p) + (2 * lam * (SmallMassExpressions.cap28 lam S) * (p^2)) + (-1 * lam * (SmallMassExpressions.cap28 lam S) * (SmallMassExpressions.score lam S p) * p))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := ((SmallMassExpressions.cap28 lam S) * ((SmallMassExpressions.denominator lam S p)^2))


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (SmallMassExpressions.rateSlope lam S p (SmallMassExpressions.cap28 lam S))*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨52451282027786215101471179466159723267412546397639511514188919773578278607226675, 0, 4, 0, 0, 0, 0⟩,
  ⟨261017064459984446868609532733341511355601055211062455791590173262954665799157300, 1, 3, 0, 0, 0, 0⟩,
  ⟨471544281478802490732935529346910060223668087166521870574701527316884107830483214, 2, 2, 0, 0, 0, 0⟩,
  ⟨369386204101602151469417609381061073892906848558384422409780294259217332692401228, 3, 1, 0, 0, 0, 0⟩,
  ⟨106430364788414341965355615375057786264850202593088527323571790991709612053848639, 4, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (3309906285535883008509809214042738209898240000000000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((1/5)+(127/2000)*x)=
      52451282027786215101471179466159723267412546397639511514188919773578278607226675+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<52451282027786215101471179466159723267412546397639511514188919773578278607226675 := by norm_num
  have hs : (0:ℝ)<3309906285535883008509809214042738209898240000000000000000000000000000000000000000 := by norm_num
  have hprod : 0<(3309906285535883008509809214042738209898240000000000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((1/5):ℝ) (527/2000))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(SmallMassExpressions.rateSlope (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (SmallMassExpressions.cap28 (StaticLow.lam:ℝ) (StaticLow.slack:ℝ))) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(SmallMassExpressions.rateSlope (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (SmallMassExpressions.cap28 (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)))*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.CapRateSlope


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.CapSplitMargin
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
  ⟨28122934778774512976233914504722301402731183, 0, 2, 0, 0, 0, 0⟩,
  ⟨42682657581776604901012674334304077512182366, 1, 1, 0, 0, 0, 0⟩,
  ⟨14398514825131902111601688766667297094142983, 2, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (506457591003276164796022200000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((1/5)+(127/2000)*x)=
      14398514825131902111601688766667297094142983+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<14398514825131902111601688766667297094142983 := by norm_num
  have hs : (0:ℝ)<506457591003276164796022200000000000000000 := by norm_num
  have hprod : 0<(506457591003276164796022200000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((1/5):ℝ) (527/2000))
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

end OptimalG.Certificates.StaticSmallMassLinks.CapSplitMargin


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.CapSupportWitness
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
  ⟨171145853955075236134658480647725970334439808897572084231025454014046412450, 0, 3, 0, 0, 0, 0⟩,
  ⟨815459734019170863159857089415148715728187415113678247202218835145250192508, 1, 2, 0, 0, 0, 0⟩,
  ⟨1168975703031091292049868518452854612675691905968176233930259949922943894094, 2, 1, 0, 0, 0, 0⟩,
  ⟨521928679237729992413810312325205196291339507635635440959066568791740114036, 3, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (4269738585826064927677446821578458310743320352000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((1/5)+(127/2000)*x)=
      171145853955075236134658480647725970334439808897572084231025454014046412450+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<171145853955075236134658480647725970334439808897572084231025454014046412450 := by norm_num
  have hs : (0:ℝ)<4269738585826064927677446821578458310743320352000000000000000000000000000 := by norm_num
  have hprod : 0<(4269738585826064927677446821578458310743320352000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((1/5):ℝ) (527/2000))
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

end OptimalG.Certificates.StaticSmallMassLinks.CapSupportWitness


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.CapTarget
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
  ⟨15511519998927154235200594366980795549363483459, 0, 3, 0, 0, 0, 0⟩,
  ⟨47957588758943081750343161940774668380388362023, 1, 2, 0, 0, 0, 0⟩,
  ⟨47358541213268757569721944923365389270755834305, 2, 1, 0, 0, 0, 0⟩,
  ⟨15106988538183842024630634288715753939730955741, 3, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (1519372773009828494388066600000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((1/5)+(127/2000)*x)=
      15106988538183842024630634288715753939730955741+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<15106988538183842024630634288715753939730955741 := by norm_num
  have hs : (0:ℝ)<1519372773009828494388066600000000000000000000000 := by norm_num
  have hprod : 0<(1519372773009828494388066600000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((1/5):ℝ) (527/2000))
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

end OptimalG.Certificates.StaticSmallMassLinks.CapTarget
