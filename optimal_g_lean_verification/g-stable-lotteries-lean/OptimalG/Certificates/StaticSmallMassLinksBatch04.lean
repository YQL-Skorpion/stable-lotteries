import OptimalG.Certificates.SmallMassExpressions
import OptimalG.Certificates.StaticLowParameters
import OptimalG.Certificates.TensorBernstein


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.DirectHeadZero2
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := (((SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S) * p) + ((SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.cap28 lam S)) + (lam * (SmallMassExpressions.cap28 lam S) * (SmallMassExpressions.primitive lam S p)) + ((SmallMassExpressions.cap28 lam S) * (SmallMassExpressions.primitive lam S p) * p) + (-1 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S) * (SmallMassExpressions.cap28 lam S)) + (-1 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap28 lam S) * p) + (-1 * (SmallMassExpressions.initial lam S) * lam * (SmallMassExpressions.primitive lam S p)) + (-1 * (SmallMassExpressions.initial lam S) * (SmallMassExpressions.primitive lam S p) * p))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := ((SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.cap28 lam S))


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (SmallMassExpressions.target lam S p-SmallMassExpressions.etaTwo lam S p*SmallMassExpressions.initial lam S)*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨518133993691822009932406833177342277372897255614264906890326963744751548771416124941604448632829501494703453, 0, 3, 0, 0, 0, 0⟩,
  ⟨1275327939256489970572290138704747221081406019167003988162237057699549066833104836320673374950564978788203199, 1, 2, 0, 0, 0, 0⟩,
  ⟨1711936876351969815452410676311077014511023495186977692124445890032644407977965928652191141985203111292920039, 2, 1, 0, 0, 0, 0⟩,
  ⟨869885975620716461663917259665662655239318957674133870359424508266728879152689167273122215667467633999420293, 3, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (935554840841112429399774382319724225247922285448769071000456960000000000000000000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((1/25)+(1/10)*x)=
      425109313085496656857430046234915740360468673055667996054079019233183022277701612106891124983521659596067733+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<425109313085496656857430046234915740360468673055667996054079019233183022277701612106891124983521659596067733 := by norm_num
  have hs : (0:ℝ)<935554840841112429399774382319724225247922285448769071000456960000000000000000000000000000000000000000000000000 := by norm_num
  have hprod : 0<(935554840841112429399774382319724225247922285448769071000456960000000000000000000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((1/25):ℝ) (7/50))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(SmallMassExpressions.target (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p-SmallMassExpressions.etaTwo (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*SmallMassExpressions.initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(SmallMassExpressions.target (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p-SmallMassExpressions.etaTwo (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*SmallMassExpressions.initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ))*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.DirectHeadZero2


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.HeadBetaDerivative
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
  ⟨47833907442071239545565959682720220098905563, 0, 2, 0, 0, 0, 0⟩,
  ⟨77695262914865565773650019672707429005193846, 1, 1, 0, 0, 0, 0⟩,
  ⟨29093658579484475588748623669764535325808283, 2, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (253228795501638082398011100000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((7/50)+(3/50)*x)=
      29093658579484475588748623669764535325808283+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<29093658579484475588748623669764535325808283 := by norm_num
  have hs : (0:ℝ)<253228795501638082398011100000000000000000000 := by norm_num
  have hprod : 0<(253228795501638082398011100000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((7/50):ℝ) (1/5))
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

end OptimalG.Certificates.StaticSmallMassLinks.HeadBetaDerivative


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.HeadRateLeft
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := ((391 * ((SmallMassExpressions.denominator lam S p)^2)) + (-891 * (SmallMassExpressions.primitive lam S p) * (lam^2)) + (-500 * lam * ((SmallMassExpressions.denominator lam S p)^2)) + (-391 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.primitive lam S p)) + (-391 * (SmallMassExpressions.initial lam S) * (p^2)) + (-391 * (SmallMassExpressions.primitive lam S p) * (p^2)) + (-250 * (SmallMassExpressions.initial lam S) * (p^4)) + (391 * lam * (SmallMassExpressions.primitive lam S p)) + (391 * (SmallMassExpressions.primitive lam S p) * p) + (500 * (SmallMassExpressions.primitive lam S p) * (lam^3)) + (641 * (SmallMassExpressions.initial lam S) * (p^3)) + (-1282 * lam * (SmallMassExpressions.primitive lam S p) * p) + (-1250 * (SmallMassExpressions.initial lam S) * (lam^2) * (p^2)) + (-1000 * (SmallMassExpressions.initial lam S) * lam * (p^3)) + (-750 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S) * (p^2)) + (-500 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S) * (lam^2)) + (-500 * (SmallMassExpressions.initial lam S) * p * (lam^3)) + (-500 * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p) * (lam^2)) + (-391 * (SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.score lam S p)) + (-391 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.score lam S p) * p) + (-391 * (SmallMassExpressions.initial lam S) * lam * p) + (-391 * (SmallMassExpressions.initial lam S) * (SmallMassExpressions.score lam S p) * (p^2)) + (250 * (SmallMassExpressions.initial lam S) * (SmallMassExpressions.score lam S p) * (p^3)) + (391 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S) * lam) + (391 * lam * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p)) + (391 * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p) * p) + (500 * (SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.primitive lam S p)) + (500 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.score lam S p) * (lam^2)) + (500 * lam * (SmallMassExpressions.primitive lam S p) * (p^2)) + (782 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S) * p) + (891 * (SmallMassExpressions.initial lam S) * p * (lam^2)) + (1000 * (SmallMassExpressions.primitive lam S p) * p * (lam^2)) + (1532 * (SmallMassExpressions.initial lam S) * lam * (p^2)) + (-1500 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S) * lam * p) + (-500 * lam * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p) * p) + (-391 * (SmallMassExpressions.initial lam S) * lam * (SmallMassExpressions.score lam S p) * p) + (500 * (SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.score lam S p) * p) + (500 * (SmallMassExpressions.initial lam S) * (SmallMassExpressions.score lam S p) * p * (lam^2)) + (750 * (SmallMassExpressions.initial lam S) * lam * (SmallMassExpressions.score lam S p) * (p^2)))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := (500 * (SmallMassExpressions.initial lam S) * ((SmallMassExpressions.denominator lam S p)^2))


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (SmallMassExpressions.rateLeft lam S p (SmallMassExpressions.initial lam S))*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨223294982669469466117695271763407826347256740227331520871903853641260686060699899283, 0, 4, 0, 0, 0, 0⟩,
  ⟨850433019562041426959869176242394109908300639865375504077353994980964963857505586836, 1, 3, 0, 0, 0, 0⟩,
  ⟨1107166558491674284505802735874838594306773397539944389533721948683640490026376875898, 2, 2, 0, 0, 0, 0⟩,
  ⟨537803678484016746024329774660311033868668437254084899389544842006774970705233388420, 3, 1, 0, 0, 0, 0⟩,
  ⟨58502509312353381214667800344303794953997910227291643775958385567713686649806200075, 4, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (405596602600951546585445213227089018316465754100000000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((7/50)+(3/50)*x)=
      58502509312353381214667800344303794953997910227291643775958385567713686649806200075+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<58502509312353381214667800344303794953997910227291643775958385567713686649806200075 := by norm_num
  have hs : (0:ℝ)<405596602600951546585445213227089018316465754100000000000000000000000000000000000000 := by norm_num
  have hprod : 0<(405596602600951546585445213227089018316465754100000000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((7/50):ℝ) (1/5))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(SmallMassExpressions.rateLeft (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (SmallMassExpressions.initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ))) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(SmallMassExpressions.rateLeft (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (SmallMassExpressions.initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)))*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.HeadRateLeft


/-! A fixed-candidate univariate C4 sign. Generated proposals are verified
by exact polynomial equality and kernel-checked integer coefficients. -/
namespace OptimalG.Certificates.StaticSmallMassLinks.HeadRateRight
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def semanticNumerator (lam S p : ℝ) : ℝ := ((1000 * ((SmallMassExpressions.denominator lam S p)^2)) + (-1000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.primitive lam S p)) + (-1000 * (SmallMassExpressions.initial lam S) * (p^2)) + (-1000 * (SmallMassExpressions.primitive lam S p) * (lam^2)) + (-1000 * (SmallMassExpressions.primitive lam S p) * (p^2)) + (-500 * (SmallMassExpressions.initial lam S) * (p^4)) + (-109 * (SmallMassExpressions.initial lam S) * (lam^2)) + (109 * (SmallMassExpressions.initial lam S) * (lam^3)) + (1000 * lam * (SmallMassExpressions.primitive lam S p)) + (1000 * (SmallMassExpressions.primitive lam S p) * p) + (1500 * (SmallMassExpressions.initial lam S) * (p^3)) + (-2500 * (SmallMassExpressions.initial lam S) * (lam^2) * (p^2)) + (-2000 * (SmallMassExpressions.initial lam S) * lam * (p^3)) + (-2000 * lam * (SmallMassExpressions.primitive lam S p) * p) + (-1500 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S) * (p^2)) + (-1109 * (SmallMassExpressions.initial lam S) * lam * p) + (-1000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S) * (lam^2)) + (-1000 * (SmallMassExpressions.denominator lam S p) * lam * (SmallMassExpressions.score lam S p)) + (-1000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.score lam S p) * p) + (-1000 * (SmallMassExpressions.initial lam S) * (SmallMassExpressions.score lam S p) * (p^2)) + (-1000 * (SmallMassExpressions.initial lam S) * p * (lam^3)) + (-109 * (SmallMassExpressions.initial lam S) * (SmallMassExpressions.score lam S p) * (lam^2)) + (500 * (SmallMassExpressions.initial lam S) * (SmallMassExpressions.score lam S p) * (p^3)) + (1000 * lam * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p)) + (1000 * (SmallMassExpressions.primitive lam S p) * (SmallMassExpressions.score lam S p) * p) + (1109 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S) * lam) + (2000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S) * p) + (2218 * (SmallMassExpressions.initial lam S) * p * (lam^2)) + (3609 * (SmallMassExpressions.initial lam S) * lam * (p^2)) + (-3000 * (SmallMassExpressions.denominator lam S p) * (SmallMassExpressions.initial lam S) * lam * p) + (-1109 * (SmallMassExpressions.initial lam S) * lam * (SmallMassExpressions.score lam S p) * p) + (1000 * (SmallMassExpressions.initial lam S) * (SmallMassExpressions.score lam S p) * p * (lam^2)) + (1500 * (SmallMassExpressions.initial lam S) * lam * (SmallMassExpressions.score lam S p) * (p^2)))
noncomputable def semanticDenominator (lam S p : ℝ) : ℝ := (1000 * (SmallMassExpressions.initial lam S) * ((SmallMassExpressions.denominator lam S p)^2))


theorem rational_identity {lam S p : ℝ}
    (hD : SmallMassExpressions.denominator lam S p≠0)
    (hF : SmallMassExpressions.initial lam S≠0)
    (hM : SmallMassExpressions.cap28 lam S≠0)
    (hW : SmallMassExpressions.cap2918 lam S≠0) :
    (SmallMassExpressions.rateRight lam S p (SmallMassExpressions.initial lam S))*semanticDenominator lam S p=semanticNumerator lam S p := by
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
  ⟨16909782677044145790118445234948621289378177110885219028138008097237293220453479360111, 0, 4, 0, 0, 0, 0⟩,
  ⟨329345954386928642311051786794809618833190624990044552332180691202638137956672165687084, 1, 3, 0, 0, 0, 0⟩,
  ⟨887514240459979608550646033235735074586158974062885633049349427713020698504414045483786, 2, 2, 0, 0, 0, 0⟩,
  ⟨848589519903279683838670354750193709750233800554581690625433617345576876717955031346764, 3, 1, 0, 0, 0, 0⟩,
  ⟨273750087807927029188182633738696333059887885362601557090786237069992262175881272189951, 4, 0, 0, 0, 0, 0⟩]
theorem certificate_checked : certificate.check=true := by decide +kernel

theorem certificate_identity (x : ℝ) :
    (30419745195071365993908390992031676373734931557500000000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack ((7/50)+(3/50)*x)=
      16909782677044145790118445234948621289378177110885219028138008097237293220453479360111+certificate.eval x 0 0 := by
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
  have hm : (0:ℝ)<16909782677044145790118445234948621289378177110885219028138008097237293220453479360111 := by norm_num
  have hs : (0:ℝ)<30419745195071365993908390992031676373734931557500000000000000000000000000000000000000 := by norm_num
  have hprod : 0<(30419745195071365993908390992031676373734931557500000000000000000000000000000000000000:ℝ)*semanticNumerator StaticLow.lam StaticLow.slack p := by linarith only [hh,he,hm]
  exact (mul_pos_iff_of_pos_left hs).mp hprod

theorem coefficient_positive {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc ((7/50):ℝ) (1/5))
    (hD : 0<SmallMassExpressions.denominator StaticLow.lam StaticLow.slack p)
    (hF : 0<SmallMassExpressions.initial StaticLow.lam StaticLow.slack)
    (hM : 0<SmallMassExpressions.cap28 StaticLow.lam StaticLow.slack)
    (hW : 0<SmallMassExpressions.cap2918 StaticLow.lam StaticLow.slack) :
    0<(SmallMassExpressions.rateRight (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (SmallMassExpressions.initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ))) := by
  have hn := numerator_positive hp
  have hd : 0<semanticDenominator StaticLow.lam StaticLow.slack p := by
    unfold semanticDenominator
    positivity
  have he := rational_identity (ne_of_gt hD) (ne_of_gt hF) (ne_of_gt hM) (ne_of_gt hW)
  have hm : 0<(SmallMassExpressions.rateRight (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (SmallMassExpressions.initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)))*semanticDenominator StaticLow.lam StaticLow.slack p := by rw [he]; exact hn
  exact (mul_pos_iff_of_pos_right hd).mp hm

end OptimalG.Certificates.StaticSmallMassLinks.HeadRateRight
