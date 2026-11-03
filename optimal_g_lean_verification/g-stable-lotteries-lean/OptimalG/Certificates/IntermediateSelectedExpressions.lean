import OptimalG.Certificates.IntermediateTailExpressions
import OptimalG.LargeMassSplitBounds

/-! Scalar residuals for intermediate masses before the terminal tail.
The score deficit is an explicit argument. The coefficient multiplying it
is checked before a lower bound is substituted. -/
namespace OptimalG.Certificates.IntermediateSelectedExpressions
open Set Variational IntermediateTailExpressions

noncomputable def deficitCoefficient (lam S p z : ℝ) : ℝ :=
  etaNumerator lam S p-weight lam S p*(z-391/500)/2
noncomputable def core (lam S p z e q upper lower : ℝ) : ℝ :=
  massFactor lam S p*(z+q-lam)+etaNumerator lam S p*(lam-z-e)+
    weight lam S p*(upper-(Variational.quadratic lam z-S-(z-391/500)*e/2)-lower)
noncomputable def base (lam S p z e : ℝ) : ℝ :=
  core lam S p z e 0 (Variational.quadratic lam (z-p)-S) 0
noncomputable def headCore (lam S p z e q : ℝ) : ℝ :=
  base lam S p z e+q*headLinear lam S p z-
    weight lam S p*(1+SmallMassExpressions.slope lam S)*q^2/2
noncomputable def headCleared (lam S p z e : ℝ) : ℝ :=
  2*weight lam S p*(1+SmallMassExpressions.slope lam S)*base lam S p z e+
    (headLinear lam S p z)^2
noncomputable def splitLinear (lam S p z : ℝ) : ℝ :=
  massFactor lam S p-weight lam S p*(z-p)
noncomputable def highCore (lam S p z e q E : ℝ) : ℝ :=
  base lam S p z e+q*splitLinear lam S p z+weight lam S p*(S-E)
noncomputable def capCleared (lam S p z e : ℝ) : ℝ :=
  2*weight lam S p*(9/10)*highCore lam S p z e (527/2000) (capDeficit lam S (527/2000))+
    (splitLinear lam S p z+weight lam S p*capSlack lam S (527/2000))^2
noncomputable def capCore (lam S p z e q : ℝ) : ℝ :=
  core lam S p z e q (Variational.cap lam S (z-p+q)) (SmallMassExpressions.primitive lam S q)
noncomputable def kink (lam S : ℝ) : ℝ :=
  1459/5000+capDeficit lam S (1459/5000)/capSlack lam S (1459/5000)

theorem core_antitone_deficit {lam S p z a b q upper lower : ℝ}
    (hc : 0≤deficitCoefficient lam S p z) (hab : a≤b) :
    core lam S p z b q upper lower≤core lam S p z a q upper lower := by
  have hh := mul_nonneg hc (sub_nonneg.mpr hab)
  unfold core deficitCoefficient at *
  nlinarith only [hh]

theorem headCore_identity (lam S p z e q : ℝ) :
    headCore lam S p z e q=core lam S p z e q (Variational.quadratic lam (z-p+q)-S)
      (SmallMassExpressions.primitive lam S q) := by
  unfold headCore base core headLinear Variational.quadratic SmallMassExpressions.primitive
  ring

theorem highCore_identity (lam S p z e q E : ℝ) :
    highCore lam S p z e q E=core lam S p z e q (Variational.quadratic lam (z-p+q)-S)
      (Variational.quadratic lam q-S+E) := by
  unfold highCore base core splitLinear Variational.quadratic
  ring

theorem headCore_nonpos {lam S p z e q : ℝ}
    (hw : 0<weight lam S p) (hs : 0<1+SmallMassExpressions.slope lam S)
    (hc : headCleared lam S p z e≤0) : headCore lam S p z e q≤0 := by
  have hh := concave_quadratic_nonpos (A:=base lam S p z e)
    (B:=headLinear lam S p z) (C:=weight lam S p*(1+SmallMassExpressions.slope lam S)/2)
    (x:=q) (by positivity) (by convert! hc using 1 <;> unfold headCleared <;> ring)
  convert! hh using 1 <;> unfold headCore <;> ring

theorem highCore_cap_nonpos {lam S p z e q : ℝ} (hw : 0<weight lam S p)
    (hprod : lam*S≤3/200) (hq : q∈Icc (527/2000:ℝ) (1459/5000))
    (hc : capCleared lam S p z e≤0) :
    highCore lam S p z e q (capDeficit lam S q)≤0 := by
  have hh := cap_split_nonpos (A:=base lam S p z e+weight lam S p*S)
    (B:=splitLinear lam S p z) (flat:=0) hw hprod hq
    (by convert! hc using 1 <;> unfold capCleared highCore <;> ring)
  convert! hh using 1 <;> unfold highCore <;> ring

theorem highCore_forward_nonpos {lam S p z e q : ℝ} (hw : 0≤weight lam S p)
    (hE : 0≤capDeficit lam S (1459/5000)) (hs : 0<capSlack lam S (1459/5000))
    (hq : q∈Icc (1459/5000:ℝ) lam)
    (hl : highCore lam S p z e (1459/5000) (capDeficit lam S (1459/5000))≤0)
    (hr : highCore lam S p z e lam 0≤0)
    (hk : highCore lam S p z e (kink lam S) 0≤0) :
    highCore lam S p z e q
      (max 0 (capDeficit lam S (1459/5000)-capSlack lam S (1459/5000)*(q-1459/5000)))≤0 := by
  let A := base lam S p z e+weight lam S p*S
  let B := splitLinear lam S p z
  let E := capDeficit lam S (1459/5000)
  let sig := capSlack lam S (1459/5000)
  have he (r : ℝ) : forwardSplitEnvelope A B (weight lam S p) E sig (1459/5000) r=
      highCore lam S p z e r (max 0 (E-sig*(r-1459/5000))) := by
    dsimp [A,B,E,sig,forwardSplitEnvelope,highCore]
    ring
  have hleft : forwardSplitEnvelope A B (weight lam S p) E sig (1459/5000) (1459/5000)≤0 := by
    rw [he]
    simpa only [E,sub_self,mul_zero,sub_zero,max_eq_right hE] using hl
  have hright : forwardSplitEnvelope A B (weight lam S p) E sig (1459/5000) lam≤0 := by
    rw [he]
    have hm := mul_nonneg hw (le_max_left (0:ℝ) (E-sig*(lam-1459/5000)))
    dsimp only [highCore] at hr ⊢
    linarith only [hr,hm]
  have hzero : E-sig*((1459/5000+E/sig)-1459/5000)=0 := by
    field_simp [show sig≠0 from hs.ne']
    ring
  have hbreak : forwardSplitEnvelope A B (weight lam S p) E sig (1459/5000) (1459/5000+E/sig)≤0 := by
    rw [he,hzero,max_self]
    exact hk
  have hh := forwardSplitEnvelope_nonpos (show 0<sig from hs) hleft hright hbreak q hq
  rwa [he] at hh

theorem capCore_le_endpoints {lam S p z e a b : ℝ}
    (hw : 0≤weight lam S p) (hab : a≤b) (harg : z-p+b<1)
    (hcap : ∀ u∈Icc a b,∀ v∈Icc a b,u≤v→
      SmallMassExpressions.slope lam S*(v-u)≤Variational.capScore lam S (z-p+v)-Variational.capScore lam S (z-p+u))
    (ha : capCore lam S p z e a≤0) (hb : capCore lam S p z e b≤0) :
    ∀ q∈Icc a b,capCore lam S p z e q≤0 := by
  let A := massFactor lam S p*(z-lam)+etaNumerator lam S p*(lam-z-e)-
    weight lam S p*(Variational.quadratic lam z-S-(z-391/500)*e/2)
  have he (q : ℝ) : capCore lam S p z e q=
      capHeadEnvelope lam S (z-p) (SmallMassExpressions.initial lam S)
        (SmallMassExpressions.slope lam S) A (massFactor lam S p) (weight lam S p) q := by
    dsimp [A,capHeadEnvelope,capCore,core,SmallMassExpressions.primitive]
    ring
  rw [he a] at ha
  rw [he b] at hb
  intro q hq
  rw [he q]
  exact capHeadEnvelope_le_endpoints hw hab harg hcap ha hb q hq

end OptimalG.Certificates.IntermediateSelectedExpressions
