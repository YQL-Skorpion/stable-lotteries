import OptimalG.Certificates.LargeTailExpressions
import OptimalG.CapHeadConvexity

namespace OptimalG.Certificates.LargeTailExpressions
open Set

theorem core_mono {lam p M z Y H q Ulo Uhi Llo Lhi : ℝ}
    (hp : 0≤p) (hU : Ulo≤Uhi) (hL : Llo≤Lhi) :
    core lam p M z Y H q Ulo Lhi≤core lam p M z Y H q Uhi Llo := by
  have hm := mul_nonneg hp (show 0≤(Uhi-Ulo)+(Lhi-Llo) by linarith only [hU,hL])
  unfold core
  nlinarith only [hm]

theorem headLow_nonpos {lam S p M z Y H a b q : ℝ}
    (hq : q∈Icc a b) (ha : headLow lam S p M z Y H a≤0)
    (hb : headLow lam S p M z Y H b≤0) : headLow lam S p M z Y H q≤0 := by
  by_cases hs : 0≤M+p*SmallMassExpressions.slope lam S*(z-p)
  · have hm := mul_le_mul_of_nonneg_right hq.2 hs
    unfold headLow at *
    linarith only [hm,hb]
  · have hm := mul_le_mul_of_nonpos_right hq.1 (le_of_not_ge hs)
    unfold headLow at *
    linarith only [hm,ha]

theorem capCore_as_envelope (lam S p M z Y H q : ℝ) :
    capCore lam S p M z Y H q=
      capHeadEnvelope lam S (z-p) (SmallMassExpressions.initial lam S) (SmallMassExpressions.slope lam S)
        (M*(z-lam+tailScore (539/625) Y H z)-p*tailPrimitive (539/625) Y H z) M p q := by
  rw [←capCore_identity]
  unfold core capHeadEnvelope SmallMassExpressions.primitive
  ring

theorem capCore_nonpos {lam S p M z Y H a b q : ℝ} (hp : 0≤p)
    (hab : a≤b) (harg : z-p+b<1)
    (hcap : ∀ u∈Icc a b,∀ v∈Icc a b,u≤v→
      SmallMassExpressions.slope lam S*(v-u)≤
        Variational.capScore lam S (z-p+v)-Variational.capScore lam S (z-p+u))
    (ha : capCore lam S p M z Y H a≤0) (hb : capCore lam S p M z Y H b≤0)
    (hq : q∈Icc a b) : capCore lam S p M z Y H q≤0 := by
  rw [capCore_as_envelope] at ha hb ⊢
  exact capHeadEnvelope_le_endpoints hp hab harg hcap ha hb q hq

end OptimalG.Certificates.LargeTailExpressions
