import OptimalG.Certificates.SmallMassExpressions
import OptimalG.TailAnchorOrder
import OptimalG.CapHeadConvexity
import OptimalG.PositivePartQuadratic

/-! Explicit scalar residuals for intermediate masses on the terminal tail.
The complementary primitive uses its actual remaining-area allowance.
Only the full head-square test is used; no head-linear sign is required. -/
namespace OptimalG.Certificates.IntermediateTailExpressions
open Set Variational

noncomputable def massPrimitive (lam S p : ℝ) : ℝ := Variational.quadratic lam p-S
noncomputable def complementUpper (lam S p : ℝ) : ℝ :=
  Variational.quadratic lam (1-p)-S+87/1000000000
noncomputable def headScore (lam S : ℝ) : ℝ := Variational.capScore lam S (527/2000)
noncomputable def massFactor (lam S p : ℝ) : ℝ := massPrimitive lam S p*headScore lam S
noncomputable def weight (lam S p : ℝ) : ℝ := p*headScore lam S
noncomputable def etaNumerator (lam S p : ℝ) : ℝ :=
  massFactor lam S p+lam*massPrimitive lam S p-p*complementUpper lam S p

noncomputable def base (lam S p z Y H : ℝ) : ℝ :=
  massFactor lam S p*(z-lam)+etaNumerator lam S p*tailScore (539/625) Y H z+
    weight lam S p*(Variational.quadratic lam (z-p)-S-tailPrimitive (539/625) Y H z)
noncomputable def headLinear (lam S p z : ℝ) : ℝ :=
  massFactor lam S p+weight lam S p*(lam-z+p-SmallMassExpressions.initial lam S)
noncomputable def headCore (lam S p z Y H q : ℝ) : ℝ :=
  base lam S p z Y H+q*headLinear lam S p z-
    weight lam S p*(1+SmallMassExpressions.slope lam S)*q^2/2
noncomputable def headCleared (lam S p z Y H : ℝ) : ℝ :=
  2*weight lam S p*(1+SmallMassExpressions.slope lam S)*base lam S p z Y H+
    (headLinear lam S p z)^2
noncomputable def highCore (lam S p z Y H q : ℝ) : ℝ :=
  base lam S p z Y H+q*(massFactor lam S p-weight lam S p*(z-p))+weight lam S p*S
noncomputable def capCore (lam S p z Y H q : ℝ) : ℝ :=
  headCore lam S p z Y H q+
    weight lam S p*(Variational.cap lam S (z-p+q)-Variational.quadratic lam (z-p+q)+S)

theorem headCore_identity (lam S p z Y H q : ℝ) :
    headCore lam S p z Y H q=massFactor lam S p*(z+q-lam)+
      etaNumerator lam S p*tailScore (539/625) Y H z+
      weight lam S p*(Variational.quadratic lam (z-p+q)-S-tailPrimitive (539/625) Y H z-
        SmallMassExpressions.primitive lam S q) := by
  unfold headCore headLinear base Variational.quadratic SmallMassExpressions.primitive
  ring

theorem highCore_identity (lam S p z Y H q : ℝ) :
    highCore lam S p z Y H q=massFactor lam S p*(z+q-lam)+
      etaNumerator lam S p*tailScore (539/625) Y H z+
      weight lam S p*(Variational.quadratic lam (z-p+q)-S-tailPrimitive (539/625) Y H z-
        (Variational.quadratic lam q-S)) := by
  unfold highCore base Variational.quadratic
  ring

theorem capCore_identity (lam S p z Y H q : ℝ) :
    capCore lam S p z Y H q=massFactor lam S p*(z+q-lam)+
      etaNumerator lam S p*tailScore (539/625) Y H z+
      weight lam S p*(Variational.cap lam S (z-p+q)-tailPrimitive (539/625) Y H z-
        SmallMassExpressions.primitive lam S q) := by
  rw [capCore,headCore_identity]
  ring

theorem headCore_nonpos_of_cleared {lam S p z Y H q : ℝ}
    (hw : 0<weight lam S p) (hs : 0<1+SmallMassExpressions.slope lam S)
    (hc : headCleared lam S p z Y H≤0) : headCore lam S p z Y H q≤0 := by
  have hk : 0<2*weight lam S p*(1+SmallMassExpressions.slope lam S) := by positivity
  have hsq := sq_nonneg (headLinear lam S p z-weight lam S p*(1+SmallMassExpressions.slope lam S)*q)
  have hid : (2*weight lam S p*(1+SmallMassExpressions.slope lam S))*headCore lam S p z Y H q=
      headCleared lam S p z Y H-
      (headLinear lam S p z-weight lam S p*(1+SmallMassExpressions.slope lam S)*q)^2 := by
    unfold headCore headCleared
    ring
  have hh : (2*weight lam S p*(1+SmallMassExpressions.slope lam S))*headCore lam S p z Y H q≤0 := by
    rw [hid]
    linarith only [hc,hsq]
  exact nonpos_of_mul_nonpos_right hh hk

theorem highCore_le_endpoints {lam S p z Y H a b : ℝ}
    (ha : highCore lam S p z Y H a≤0) (hb : highCore lam S p z Y H b≤0) :
    ∀ q∈Icc a b,highCore lam S p z Y H q≤0 := by
  have he (q : ℝ) : highCore lam S p z Y H q=
      (base lam S p z Y H+weight lam S p*S)+
      (massFactor lam S p-weight lam S p*(z-p))*q+
      (0:ℝ)*(max ((0:ℝ)+0*q) 0)^2 := by unfold highCore; ring
  rw [he a] at ha
  rw [he b] at hb
  intro q hq
  rw [he q]
  exact positive_affine_square_le_endpoints (by norm_num : (0:ℝ)≤0) ha hb q hq

theorem capCore_le_endpoints {lam S p z Y H a b : ℝ}
    (hw : 0≤weight lam S p) (hab : a≤b) (harg : z-p+b<1)
    (hcap : ∀ u∈Icc a b,∀ v∈Icc a b,u≤v→
      SmallMassExpressions.slope lam S*(v-u)≤Variational.capScore lam S (z-p+v)-Variational.capScore lam S (z-p+u))
    (ha : capCore lam S p z Y H a≤0) (hb : capCore lam S p z Y H b≤0) :
    ∀ q∈Icc a b,capCore lam S p z Y H q≤0 := by
  let A := massFactor lam S p*(z-lam)+etaNumerator lam S p*tailScore (539/625) Y H z-
    weight lam S p*tailPrimitive (539/625) Y H z
  have he (q : ℝ) : capCore lam S p z Y H q=
      capHeadEnvelope lam S (z-p) (SmallMassExpressions.initial lam S)
        (SmallMassExpressions.slope lam S) A (massFactor lam S p) (weight lam S p) q := by
    rw [capCore_identity]
    dsimp [A,capHeadEnvelope,SmallMassExpressions.primitive]
    ring
  rw [he a] at ha
  rw [he b] at hb
  intro q hq
  rw [he q]
  exact capHeadEnvelope_le_endpoints hw hab harg hcap ha hb q hq

end OptimalG.Certificates.IntermediateTailExpressions
