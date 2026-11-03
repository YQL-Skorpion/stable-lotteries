import OptimalG.Certificates.StaticLowParameters
import OptimalG.Certificates.SmallMassExpressions
import OptimalG.BinaryCentralCertificate

namespace OptimalG.Certificates.StaticBinaryCentralExpressions
open Set Variational
noncomputable def L : ℝ := StaticLow.lam
noncomputable def S : ℝ := StaticLow.slack
noncomputable def c : ℝ := StaticLow.leftContact
noncomputable def initial : ℝ := SmallMassExpressions.initial L S
noncomputable def slope : ℝ := SmallMassExpressions.slope L S
noncomputable def base (p q : ℝ) : ℝ :=
  Variational.quadratic L p-S+p*(L/2-initial-slope*q/2)-L*S/(p-q)
noncomputable def capError (p q : ℝ) : ℝ :=
  Variational.quadratic L (q+1-p)-S+Variational.capDeficit L S c-Variational.capSlack L S c*(q+1-p-c)+
    (309/2000)*(q+1-p-c)^2-Variational.cap L S (q+1-p)
noncomputable def rightError (p q : ℝ) : ℝ :=
  Variational.quadratic L (q+1-p)-S+87/1000000000-Variational.cap L S (q+1-p)
noncomputable def middleError (p q : ℝ) : ℝ :=
  Variational.quadratic L (q+1-p)-S-Variational.cap L S (q+1-p)
noncomputable def actualError (p q : ℝ) : ℝ :=
  binaryHeadCapError L S initial slope (527/2000) c (q+1-p)

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem contact_left : (527/2000:ℝ)<c := by
  norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
theorem contact_discriminant : (Variational.capSlack L S c)^2≤(309/500)*Variational.capDeficit L S c := by
  norm_num [L,S,c,StaticLow.lam,StaticLow.slack,StaticLow.leftContact,
    UpperProfileData.leftContact,Variational.capSlack,Variational.capDeficit,Variational.cap,Variational.capScore,Variational.quadratic]

theorem cap_envelope {p q : ℝ} (hr : c≤q+1-p) : actualError p q≤capError p q :=
  binaryHeadCapError_le_cap_envelope contact_left hr contact_discriminant

theorem right_envelope {p q : ℝ} (hc : c≤q+1-p)
    (hr : (348541/1000000:ℝ)≤q+1-p) : actualError p q≤rightError p q :=
  binaryHeadCapError_le_right_envelope contact_left hc hr

theorem middle_envelope {p q : ℝ} (hr : (9/25:ℝ)≤q+1-p) :
    actualError p q=middleError p q := by
  unfold actualError binaryHeadCapError middleError
  rw [if_neg (by linarith only [hr] : ¬q+1-p≤(527/2000:ℝ)),if_pos hr]

end OptimalG.Certificates.StaticBinaryCentralExpressions
