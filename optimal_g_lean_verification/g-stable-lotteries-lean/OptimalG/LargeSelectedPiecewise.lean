import OptimalG.LargeSelectedMassReduction
import OptimalG.Certificates.SmallMassExpressions

namespace OptimalG
open Set Variational

/-- Join two antitone closed-interval pieces, allowing the cut to lie
outside the interval. Values at a shared endpoint are counted in both. -/
theorem antitoneOn_interval_split {f : ℝ→ℝ} {a b c : ℝ}
    (hl : AntitoneOn f (Icc a (min b c)))
    (hr : AntitoneOn f (Icc (max a c) b)) : AntitoneOn f (Icc a b) := by
  intro x hx y hy hxy
  by_cases hyc : y≤c
  · exact hl ⟨hx.1,le_min hx.2 (hxy.trans hyc)⟩ ⟨hy.1,le_min hy.2 hyc⟩ hxy
  · by_cases hcx : c≤x
    · exact hr ⟨max_le hx.1 hcx,hx.2⟩ ⟨max_le hy.1 (hcx.trans hxy),hy.2⟩ hxy
    · have hxc : x≤c := le_of_not_ge hcx
      have hcy : c≤y := le_of_not_ge hyc
      have hac : a≤c := hx.1.trans hxc
      have hcb : c≤b := hcy.trans hy.2
      exact (hr ⟨max_le hac le_rfl,hcb⟩ ⟨max_le hy.1 hcy,hy.2⟩ hcy).trans
        (hl ⟨hx.1,le_min hx.2 hxc⟩ ⟨hac,le_min hcb le_rfl⟩ hxc)

/-- A smooth envelope branch needs only its derivative numerator sign. -/
theorem largeSelected_branch_antitone {lam S z q e lower a b : ℝ}
    {upper du : ℝ→ℝ}
    (hu : ∀ p∈Icc a b,HasDerivAt upper (du (z-p+q)) (z-p+q))
    (hn : ∀ p∈Icc a b,
      largeSelectedMassDerivative lam S p z q e (upper (z-p+q)) lower (du (z-p+q))≤0) :
    AntitoneOn (largeSelectedNumerator lam S z q e lower upper) (Icc a b) := by
  have hd (p : ℝ) (hp : p∈Icc a b) :=
    largeSelectedNumerator_hasDerivAt (lam:=lam) (S:=S) (e:=e) (lower:=lower) (hu p hp)
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    (fun p hp=>(hd p hp).continuousAt.continuousWithinAt)
    (fun p hp=>(hd p (interior_subset hp)).differentiableAt.differentiableWithinAt)
  intro p hp
  rw [(hd p (interior_subset hp)).deriv]
  exact hn p (interior_subset hp)

noncomputable def largeHeadRemaining (lam S r : ℝ) : ℝ :=
  Certificates.SmallMassExpressions.primitive lam S r-quadratic lam r+S

theorem largeHeadRemaining_hasDerivAt (lam S r : ℝ) :
    HasDerivAt (largeHeadRemaining lam S)
      (Certificates.SmallMassExpressions.initial lam S-lam+
        (1+Certificates.SmallMassExpressions.slope lam S)*r) r := by
  have hh := (((hasDerivAt_id r).const_mul (Certificates.SmallMassExpressions.initial lam S)).add
    (((hasDerivAt_id r).pow 2).const_mul (Certificates.SmallMassExpressions.slope lam S) |>.div_const 2))
  convert! (hh.sub (quadratic_hasDerivAt lam r)).add_const S using 1 <;>
    dsimp [largeHeadRemaining,Certificates.SmallMassExpressions.primitive] <;> ring

theorem largeRemainingUpper_eq_head {lam S r : ℝ} (hr : r≤527/2000) :
    largeRemainingUpper lam S (Certificates.SmallMassExpressions.initial lam S)
      (Certificates.SmallMassExpressions.slope lam S) r=largeHeadRemaining lam S r := by
  rw [largeRemainingUpper,if_pos hr]
  rfl

theorem largeRemainingUpper_eq_cap {lam S r : ℝ}
    (hr : r∈Icc (527/2000:ℝ) (313/1000)) :
    largeRemainingUpper lam S (Certificates.SmallMassExpressions.initial lam S)
      (Certificates.SmallMassExpressions.slope lam S) r=capDeficit lam S r := by
  by_cases hh : r≤527/2000
  · have he : r=527/2000 := le_antisymm hh hr.1
    subst r
    rw [largeRemainingUpper,if_pos le_rfl]
    have hj := headPrimitive_at_join (527/2000) (cap lam S (527/2000))
      (capScore lam S (527/2000)) (by norm_num)
    change Certificates.SmallMassExpressions.primitive lam S (527/2000)=cap lam S (527/2000) at hj
    change Certificates.SmallMassExpressions.primitive lam S (527/2000)-quadratic lam (527/2000)+S=
      capDeficit lam S (527/2000)
    rw [hj]
    unfold capDeficit
    ring
  · rw [largeRemainingUpper,if_neg hh,if_pos hr.2]

theorem largeRemainingUpper_eq_flat {lam S r : ℝ} (hr : 313/1000≤r) :
    largeRemainingUpper lam S (Certificates.SmallMassExpressions.initial lam S)
      (Certificates.SmallMassExpressions.slope lam S) r=capDeficit lam S (313/1000) := by
  have hh : ¬r≤527/2000 := by linarith only [hr]
  rw [largeRemainingUpper,if_neg hh]
  by_cases hf : r≤313/1000
  · have he : r=313/1000 := le_antisymm hf hr
    rw [if_pos hf,he]
  · rw [if_neg hf]

end OptimalG
