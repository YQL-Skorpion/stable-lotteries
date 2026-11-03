import OptimalG.LargeSelectedMassReduction
import OptimalG.LargeMassSplitBounds
import OptimalG.Certificates.LineControlExpressions
import OptimalG.Certificates.SmallMassExpressions
import OptimalG.CubicControlDeficit

namespace OptimalG.Certificates.LargeSelectedExpressions
open Set Variational

noncomputable def cubic (lam S z : ℝ) : ℝ :=
  cubicControlDeficit (LineControl.slope lam S) (LineControl.alpha lam S) (LineControl.crossing lam S) z
noncomputable def areaSlope (lam S p z : ℝ) : ℝ := p*(z-lam)-p^2/2+S
noncomputable def flat (lam S : ℝ) : ℝ := Variational.capDeficit lam S (313/1000)
noncomputable def primitiveCap (lam S p : ℝ) : ℝ := Variational.quadratic lam p-S
noncomputable def flatNumerator (lam S p z e q E : ℝ) : ℝ :=
  (p-q)*areaSlope lam S p z+p*(flat lam S-E)-
    (primitiveCap lam S p-p*(z-391/500)/2)*e
noncomputable def atMass (lam S z q E : ℝ) : ℝ :=
  flatNumerator lam S (13/20) z (cubic lam S z) q E
noncomputable def massDerivativeBound (lam S p b C D : ℝ) : ℝ :=
  areaSlope lam S p (7/8)+(p-b)*(7/8-lam-p)+D+p*C+(p-lam+93/2000)*(13/200)
noncomputable def headMassDerivative (lam S p : ℝ) : ℝ :=
  massDerivativeBound lam S p (527/2000) (lam-SmallMassExpressions.initial lam S) S
noncomputable def middleMassDerivative (lam S p : ℝ) : ℝ :=
  massDerivativeBound lam S p (9/25) (1/20) S
noncomputable def lateMassDerivative (lam S p : ℝ) : ℝ :=
  massDerivativeBound lam S p lam 0 (3/10000)
noncomputable def headHeadDerivative (lam S z : ℝ) : ℝ :=
  -areaSlope lam S (13/20) z+(13/20)*(1+SmallMassExpressions.slope lam S)*(z-13/20)
noncomputable def headFlatDerivative (lam S z : ℝ) : ℝ :=
  -areaSlope lam S (13/20) z+(13/20)*capSlack lam S (527/2000)
noncomputable def capMaximum (lam S z : ℝ) : ℝ :=
  (9/5)*(13/20)*atMass lam S z (527/2000) (capDeficit lam S (527/2000))+
    (headFlatDerivative lam S z)^2
noncomputable def kink (lam S : ℝ) : ℝ :=
  1459/5000+capDeficit lam S (1459/5000)/capSlack lam S (1459/5000)
noncomputable def smallSplitK (lam S z : ℝ) : ℝ :=
  SmallMassExpressions.primitive lam S (z-13/20)-Variational.quadratic lam z+S+
    (z-391/500)*cubic lam S z/2

theorem flatNumerator_identity (lam S p z e q E : ℝ) :
    flatNumerator lam S p z e q E=
      largeSelectedNumerator lam S z q e E (fun _=>flat lam S) p := by
  rfl

theorem flatNumerator_cap_nonpos {lam S p z e q : ℝ} (hp : 0<p)
    (hprod : lam*S≤3/200) (hq : q∈Icc (527/2000:ℝ) (1459/5000))
    (hc : 2*p*(9/10)*flatNumerator lam S p z e (527/2000) (capDeficit lam S (527/2000))+
      (-areaSlope lam S p z+p*capSlack lam S (527/2000))^2≤0) :
    flatNumerator lam S p z e q (capDeficit lam S q)≤0 := by
  have hh := cap_split_nonpos
    (A:=p*areaSlope lam S p z-(primitiveCap lam S p-p*(z-391/500)/2)*e)
    (B:= -areaSlope lam S p z) (flat:=flat lam S) hp hprod hq
    (by convert! hc using 1 <;> unfold flatNumerator <;> ring)
  convert! hh using 1 <;> unfold flatNumerator <;> ring

theorem flatNumerator_forward_nonpos {lam S p z e q : ℝ} (hp : 0≤p)
    (hE : 0≤capDeficit lam S (1459/5000)) (hs : 0<capSlack lam S (1459/5000))
    (hq : q∈Icc (1459/5000:ℝ) lam)
    (hl : flatNumerator lam S p z e (1459/5000) (capDeficit lam S (1459/5000))≤0)
    (hr : flatNumerator lam S p z e lam 0≤0)
    (hk : flatNumerator lam S p z e (kink lam S) 0≤0) :
    flatNumerator lam S p z e q
      (max 0 (capDeficit lam S (1459/5000)-capSlack lam S (1459/5000)*(q-1459/5000)))≤0 := by
  let A := p*(areaSlope lam S p z+flat lam S)-(primitiveCap lam S p-p*(z-391/500)/2)*e
  let B := -areaSlope lam S p z
  let E := capDeficit lam S (1459/5000)
  let sig := capSlack lam S (1459/5000)
  have he (r : ℝ) : forwardSplitEnvelope A B p E sig (1459/5000) r=
      flatNumerator lam S p z e r (max 0 (E-sig*(r-1459/5000))) := by
    dsimp [A,B,E,sig,forwardSplitEnvelope,flatNumerator]
    ring
  have hleft : forwardSplitEnvelope A B p E sig (1459/5000) (1459/5000)≤0 := by
    rw [he]
    simpa only [E,sub_self,mul_zero,sub_zero,max_eq_right hE] using hl
  have hright : forwardSplitEnvelope A B p E sig (1459/5000) lam≤0 := by
    rw [he]
    have hm := mul_nonneg hp (le_max_left (0:ℝ) (E-sig*(lam-1459/5000)))
    dsimp only [flatNumerator] at hr ⊢
    linarith only [hr,hm]
  have hzero : E-sig*((1459/5000+E/sig)-1459/5000)=0 := by
    field_simp [show sig≠0 from hs.ne']
    ring
  have hbreak : forwardSplitEnvelope A B p E sig (1459/5000) (1459/5000+E/sig)≤0 := by
    rw [he,hzero,max_self]
    exact hk
  have hh := forwardSplitEnvelope_nonpos (show 0<sig from hs) hleft hright hbreak q hq
  rwa [he] at hh

end OptimalG.Certificates.LargeSelectedExpressions
