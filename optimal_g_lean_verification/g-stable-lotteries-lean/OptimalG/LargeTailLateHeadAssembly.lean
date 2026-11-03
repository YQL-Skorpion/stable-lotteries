import OptimalG.LargeTailSplitAnalytic
import OptimalG.ExtendedSlackProfiles

namespace OptimalG
open Set Variational Certificates.LargeTailExpressions

noncomputable def lateHeadCone (lam S r : ℝ) : ℝ :=
  quadratic lam r-S+87/1000000000+(3/12500)*(7/20-r)+(309/2000)*(7/20-r)^2
noncomputable def lateHeadNearLine (lam S r : ℝ) : ℝ := quadratic lam r-S+87/1000000000

structure LargeTailLateHeadSigns (lam S p M z Y H : ℝ) : Prop where
  head : ∀ r∈Icc (1/20:ℝ) (527/2000),p-z+r∈Icc (1/20:ℝ) (527/2000)→
    core lam p M z Y H (p-z+r) (Certificates.SmallMassExpressions.primitive lam S r)
      (Certificates.SmallMassExpressions.primitive lam S (p-z+r))≤0
  cap : ∀ r∈Icc (527/2000:ℝ) (313/1000),p-z+r∈Icc (1/20:ℝ) (527/2000)→
    core lam p M z Y H (p-z+r) (Variational.cap lam S r)
      (Certificates.SmallMassExpressions.primitive lam S (p-z+r))≤0
  cone : ∀ r∈Icc (313/1000:ℝ) (7/20),p-z+r∈Icc (1/20:ℝ) (527/2000)→
    core lam p M z Y H (p-z+r) (lateHeadCone lam S r)
      (Certificates.SmallMassExpressions.primitive lam S (p-z+r))≤0
  near_line : ∀ r∈Icc (7/20:ℝ) (9/25),p-z+r∈Icc (1/20:ℝ) (527/2000)→
    core lam p M z Y H (p-z+r) (lateHeadNearLine lam S r)
      (Certificates.SmallMassExpressions.primitive lam S (p-z+r))≤0
  line : ∀ r∈Icc (9/25:ℝ) (1227/2000),p-z+r∈Icc (1/20:ℝ) (527/2000)→
    core lam p M z Y H (p-z+r) (quadratic lam r-S)
      (Certificates.SmallMassExpressions.primitive lam S (p-z+r))≤0

namespace BinaryCurveGeometry
variable {phi : ℝ→ℝ} {lam S c : ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
include g

theorem lateHeadCone_upper (h : VerifierCurve phi lam)
    (harea : binarySlackArea phi lam S (7/20)≤87/1000000000)
    (hscore : scoreDefect phi lam (7/20)≤3/12500)
    {r : ℝ} (hr : r∈Icc (313/1000:ℝ) (7/20)) : curvePrimitive phi r≤lateHeadCone lam S r := by
  have hh := h.binarySlackArea_upper (c:=313/1000) (t:=9/25)
    (by norm_num) (by norm_num) (show (7/20:ℝ)∈Icc (313/1000) (9/25) by constructor <;> norm_num)
    harea hscore (k:=309/1000) (by
      intro u hu
      have hg := g.post_slope u ⟨by linarith only [hu.1,g.contact_mem.2],by linarith only [hu.2]⟩
        (7/20) ⟨by linarith only [g.contact_mem.2],by norm_num⟩ hu.2
      unfold scoreDefect
      linarith only [hg]) r ⟨hr.1,by linarith only [hr.2]⟩
  unfold binarySlackArea binaryAreaUpper at hh
  rw [max_eq_left (sub_nonneg.mpr hr.2)] at hh
  unfold lateHeadCone
  linarith only [hh]

theorem fixed_large_tail_late_head_nonpos (h : VerifierCurve phi lam)
    {p M z Y H q : ℝ} (hp : p∈Icc (13/20:ℝ) (41/50))
    (hz : z∈Icc (97/100:ℝ) 1) (hq : q∈Icc (1/20:ℝ) (527/2000))
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial lam S)
    (harea : binarySlackArea phi lam S (7/20)≤87/1000000000)
    (hscore : scoreDefect phi lam (7/20)≤3/12500)
    (hn : LargeTailLateHeadSigns lam S p M z Y H) :
    core lam p M z Y H q (curvePrimitive phi (z-p+q)) (curvePrimitive phi q)≤0 := by
  have hp0 : 0≤p := by linarith only [hp.1]
  have head (u : ℝ) (hu : u∈Icc (0:ℝ) (527/2000)) :
      curvePrimitive phi u=Certificates.SmallMassExpressions.primitive lam S u := by
    rw [h.affine_head_primitive g.head hu,hinitial]
    rfl
  let r := z-p+q
  have hr : r∈Icc (1/20:ℝ) (1227/2000) := by
    dsimp [r]
    constructor <;> linarith only [hp.1,hp.2,hz.1,hz.2,hq.1,hq.2]
  have hr01 : r∈Icc (0:ℝ) 1 := ⟨by linarith only [hr.1],by linarith only [hr.2]⟩
  have hrel : p-z+r=q := by dsimp [r];ring
  have hqr : p-z+r∈Icc (1/20:ℝ) (527/2000) := by rwa [hrel]
  have hhead := head q ⟨by linarith only [hq.1],hq.2⟩
  by_cases hrh : r≤527/2000
  · have hu := head r ⟨hr01.1,hrh⟩
    apply (core_mono hp0 hu.le hhead.ge).trans
    simpa only [hrel] using hn.head r ⟨hr.1,hrh⟩ hqr
  · by_cases hrc : r≤313/1000
    · have hu := g.cap_upper r ⟨hr01.1,by linarith only [hrc]⟩
      apply (core_mono hp0 hu hhead.ge).trans
      simpa only [hrel] using hn.cap r ⟨le_of_not_ge hrh,hrc⟩ hqr
    · by_cases hrp : r≤7/20
      · have hu := g.lateHeadCone_upper h harea hscore ⟨le_of_not_ge hrc,hrp⟩
        apply (core_mono hp0 hu hhead.ge).trans
        simpa only [hrel] using hn.cone r ⟨le_of_not_ge hrc,hrp⟩ hqr
      · by_cases hrl : r≤9/25
        · have hh := h.binarySlackArea_antitone S
            (show (7/20:ℝ)∈Icc 0 1 by constructor <;> norm_num) hr01 (le_of_not_ge hrp)
          have hu : curvePrimitive phi r≤lateHeadNearLine lam S r := by
            unfold binarySlackArea at hh harea
            unfold lateHeadNearLine
            linarith only [hh,harea]
          apply (core_mono hp0 hu hhead.ge).trans
          simpa only [hrel] using hn.near_line r ⟨le_of_not_ge hrp,hrl⟩ hqr
        · have hu := h.primitive_le_quadratic_after_anchor (a:=9/25) (by norm_num)
            (g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩) r ⟨le_of_not_ge hrl,hr01.2⟩
          apply (core_mono hp0 hu hhead.ge).trans
          simpa only [hrel] using hn.line r ⟨le_of_not_ge hrl,hr.2⟩ hqr

end BinaryCurveGeometry
end OptimalG
