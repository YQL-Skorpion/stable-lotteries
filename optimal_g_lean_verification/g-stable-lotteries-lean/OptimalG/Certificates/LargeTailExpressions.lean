import OptimalG.Certificates.SmallMassExpressions
import OptimalG.LargeMassSplitBounds

namespace OptimalG.Certificates.LargeTailExpressions
open Set Variational

noncomputable def massCap (lam S p : ℝ) : ℝ := Variational.quadratic lam p-S
noncomputable def massLower (lam S p : ℝ) : ℝ :=
  massCap lam S p-(17/5000)*((p-391/500)/(93/1000))^2
noncomputable def flat (lam S : ℝ) : ℝ := capDeficit lam S (313/1000)
noncomputable def base (lam S p M z Y H : ℝ) : ℝ :=
  M*(z-lam+tailScore (539/625) Y H z)+
    p*(Variational.quadratic lam (z-p)-S-tailPrimitive (539/625) Y H z)
noncomputable def splitLinear (p M z : ℝ) : ℝ := M-p*(z-p)
noncomputable def headLinear (lam S p M z : ℝ) : ℝ :=
  splitLinear p M z+p*(lam-SmallMassExpressions.initial lam S)
noncomputable def flatHead (lam S p M z Y H q : ℝ) : ℝ :=
  base lam S p M z Y H+p*flat lam S+q*headLinear lam S p M z-
    p*(1+SmallMassExpressions.slope lam S)*q^2/2
noncomputable def headCleared (lam S p M z Y H : ℝ) : ℝ :=
  2*p*(1+SmallMassExpressions.slope lam S)*(base lam S p M z Y H+p*flat lam S)+
    (headLinear lam S p M z)^2
noncomputable def capCore (lam S p M z Y H q : ℝ) : ℝ :=
  base lam S p M z Y H+q*headLinear lam S p M z-
    p*(1+SmallMassExpressions.slope lam S)*q^2/2+p*capDeficit lam S (z-p+q)
noncomputable def headLow (lam S p M z Y H q : ℝ) : ℝ :=
  M*(z-lam+tailScore (539/625) Y H z)+
    p*(SmallMassExpressions.initial lam S*(z-p)+
      SmallMassExpressions.slope lam S*(z-p)^2/2-tailPrimitive (539/625) Y H z)+
    q*(M+p*SmallMassExpressions.slope lam S*(z-p))
noncomputable def flatHigh (lam S p M z Y H q E : ℝ) : ℝ :=
  base lam S p M z Y H+q*splitLinear p M z+p*(S+flat lam S-E)
noncomputable def highCapCleared (lam S p M z Y H : ℝ) : ℝ :=
  2*p*(9/10)*flatHigh lam S p M z Y H (527/2000) (capDeficit lam S (527/2000))+
    (splitLinear p M z+p*capSlack lam S (527/2000))^2
noncomputable def kink (lam S : ℝ) : ℝ :=
  1459/5000+capDeficit lam S (1459/5000)/capSlack lam S (1459/5000)
noncomputable def core (lam p M z Y H q upper lower : ℝ) : ℝ :=
  M*(z+q-lam+tailScore (539/625) Y H z)+p*(upper-tailPrimitive (539/625) Y H z-lower)

theorem flatHead_identity (lam S p M z Y H q : ℝ) :
    core lam p M z Y H q (Variational.quadratic lam (z-p+q)-S+flat lam S)
      (SmallMassExpressions.primitive lam S q)=flatHead lam S p M z Y H q := by
  unfold core flatHead base headLinear splitLinear SmallMassExpressions.primitive Variational.quadratic
  ring

theorem flatHigh_identity (lam S p M z Y H q E : ℝ) :
    core lam p M z Y H q (Variational.quadratic lam (z-p+q)-S+flat lam S)
      (Variational.quadratic lam q-S+E)=flatHigh lam S p M z Y H q E := by
  unfold core flatHigh base splitLinear Variational.quadratic
  ring

theorem capCore_identity (lam S p M z Y H q : ℝ) :
    core lam p M z Y H q (Variational.cap lam S (z-p+q))
      (SmallMassExpressions.primitive lam S q)=capCore lam S p M z Y H q := by
  unfold core capCore base headLinear splitLinear SmallMassExpressions.primitive capDeficit Variational.quadratic
  ring

theorem headLow_identity (lam S p M z Y H q : ℝ) :
    core lam p M z Y H q (SmallMassExpressions.primitive lam S (z-p+q))
      (SmallMassExpressions.primitive lam S q)=headLow lam S p M z Y H q := by
  unfold core headLow SmallMassExpressions.primitive
  ring

theorem headLow_cap_join (lam S p M z Y H : ℝ) :
    headLow lam S p M z Y H (527/2000-z+p)=capCore lam S p M z Y H (527/2000-z+p) := by
  have hjoin : SmallMassExpressions.primitive lam S (527/2000)=Variational.cap lam S (527/2000) :=
    headPrimitive_at_join (527/2000) (Variational.cap lam S (527/2000)) (capScore lam S (527/2000)) (by norm_num)
  rw [←headLow_identity,←capCore_identity]
  have he : z-p+(527/2000-z+p)=(527/2000:ℝ) := by ring
  rw [he,hjoin]

theorem flatHead_nonpos {lam S p M z Y H q : ℝ} (hp : 0<p)
    (hs : 0<1+SmallMassExpressions.slope lam S)
    (hc : headCleared lam S p M z Y H≤0) : flatHead lam S p M z Y H q≤0 := by
  have hh := concave_quadratic_nonpos
    (A:=base lam S p M z Y H+p*flat lam S) (B:=headLinear lam S p M z)
    (C:=p*(1+SmallMassExpressions.slope lam S)/2) (x:=q) (by positivity)
    (by convert! hc using 1 <;> unfold headCleared <;> ring)
  convert! hh using 1 <;> unfold flatHead <;> ring

theorem flatHigh_cap_nonpos {lam S p M z Y H q : ℝ} (hp : 0<p)
    (hprod : lam*S≤3/200) (hq : q∈Icc (527/2000:ℝ) (1459/5000))
    (hc : highCapCleared lam S p M z Y H≤0) :
    flatHigh lam S p M z Y H q (capDeficit lam S q)≤0 := by
  have hh := cap_split_nonpos (A:=base lam S p M z Y H+p*S)
    (B:=splitLinear p M z) (flat:=flat lam S) hp hprod hq
    (by convert! hc using 1 <;> unfold highCapCleared flatHigh <;> ring)
  convert! hh using 1 <;> unfold flatHigh <;> ring

theorem flatHigh_forward_nonpos {lam S p M z Y H q : ℝ} (hp : 0≤p)
    (hE : 0≤capDeficit lam S (1459/5000)) (hs : 0<capSlack lam S (1459/5000))
    (hq : q∈Icc (1459/5000:ℝ) lam)
    (hl : flatHigh lam S p M z Y H (1459/5000) (capDeficit lam S (1459/5000))≤0)
    (hr : flatHigh lam S p M z Y H lam 0≤0)
    (hk : flatHigh lam S p M z Y H (kink lam S) 0≤0) :
    flatHigh lam S p M z Y H q
      (max 0 (capDeficit lam S (1459/5000)-capSlack lam S (1459/5000)*(q-1459/5000)))≤0 := by
  let A := base lam S p M z Y H+p*(S+flat lam S)
  let B := splitLinear p M z
  let E := capDeficit lam S (1459/5000)
  let sig := capSlack lam S (1459/5000)
  have heq (r : ℝ) : forwardSplitEnvelope A B p E sig (1459/5000) r=
      flatHigh lam S p M z Y H r (max 0 (E-sig*(r-1459/5000))) := by
    dsimp [A,B,E,sig,forwardSplitEnvelope,flatHigh]
    ring
  have hleft : forwardSplitEnvelope A B p E sig (1459/5000) (1459/5000)≤0 := by
    rw [heq]
    simpa only [E,sub_self,mul_zero,sub_zero,max_eq_right hE] using hl
  have hright : forwardSplitEnvelope A B p E sig (1459/5000) lam≤0 := by
    rw [heq]
    have hm := mul_nonneg hp (le_max_left (0:ℝ) (E-sig*(lam-1459/5000)))
    dsimp only [flatHigh] at hr ⊢
    linarith only [hr,hm]
  have hzero : E-sig*((1459/5000+E/sig)-1459/5000)=0 := by
    field_simp [show sig≠0 from hs.ne']
    ring
  have hbreak : forwardSplitEnvelope A B p E sig (1459/5000) (1459/5000+E/sig)≤0 := by
    rw [heq,hzero,max_self]
    exact hk
  have hh := forwardSplitEnvelope_nonpos (show 0<sig from hs) hleft hright hbreak q hq
  rwa [heq] at hh

end OptimalG.Certificates.LargeTailExpressions
