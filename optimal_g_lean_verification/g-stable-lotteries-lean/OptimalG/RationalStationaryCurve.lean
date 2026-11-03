import OptimalG.MonotoneImplicitCurve
import OptimalG.VariationalCapSlope

/-! Exact calculus of the rational stationary branch in C.16. -/
namespace OptimalG.Variational
open Set Filter
open scoped Topology NNReal

noncomputable def capSlopeGap (lam S q : ℝ) : ℝ := 1-2*lam*S/(1-q)^3
noncomputable def stationaryLevel (lam S q : ℝ) : ℝ :=
  2*(lam-q)*capSlack lam S q-2*capDeficit lam S q

/-- The deficit derivative is minus the score deficit. -/
theorem capDeficit_hasDerivAt (lam S q : ℝ) (hq : q ≠ 1) :
    HasDerivAt (capDeficit lam S) (-capSlack lam S q) q := by
  have hd := ((hasDerivAt_const q S).sub (quadratic_hasDerivAt lam q)).add
    (cap_hasDerivAt lam S q hq)
  convert! hd using 1 <;> first | rfl | (simp only [capSlack]; ring)

theorem capSlack_hasDerivAt (lam S q : ℝ) (hq : q ≠ 1) :
    HasDerivAt (capSlack lam S) (-capSlopeGap lam S q) q := by
  have hd := ((hasDerivAt_const q lam).sub (hasDerivAt_id q)).sub
    (capScore_hasDerivAt lam S q hq)
  convert! hd using 1 <;> first | rfl | (simp only [capSlopeGap]; ring)

/-- This sign controls the monotonicity and invertibility of the stationary equation. -/
theorem stationaryLevel_hasDerivAt (lam S q : ℝ) (hq : q ≠ 1) :
    HasDerivAt (stationaryLevel lam S) (-2*(lam-q)*capSlopeGap lam S q) q := by
  have hd := ((((hasDerivAt_const q lam).sub (hasDerivAt_id q)).mul
    (capSlack_hasDerivAt lam S q hq)).const_mul 2).sub
    ((capDeficit_hasDerivAt lam S q hq).const_mul 2)
  convert! hd using 1
  · funext r
    simp only [stationaryLevel,Pi.sub_apply,Pi.mul_apply,id_eq]
    ring
  · simp only [Pi.sub_apply,id_eq]
    ring

/-- A continuous solution of the actual stationary equation is differentiable. -/
theorem stationary_branch_hasDerivAt {lam S a b p : ℝ} {q : ℝ → ℝ}
    (hp : p ∈ Ioo a b) (hq : ContinuousOn q (Icc a b))
    (hmatch : ∀ t ∈ Icc a b,stationaryLevel lam S (q t)=(1-t)^2)
    (hql : q p < lam) (hq1 : q p ≠ 1) (hgap : 0 < capSlopeGap lam S (q p)) :
    HasDerivAt q ((1-p)/((lam-q p)*capSlopeGap lam S (q p))) p := by
  have hdG := (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).pow 2)
  have hden : -2*(lam-q p)*capSlopeGap lam S (q p) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (ne_of_gt hql))) (ne_of_gt hgap)
  have hd := implicit_curve_hasDerivAt hp hq hmatch
    (stationaryLevel_hasDerivAt lam S (q p) hq1) hdG hden
  convert! hd using 1 <;> first | rfl |
    ((try simp only [Pi.sub_apply,id_eq]) <;> field_simp <;> ring)

noncomputable def stationaryBarrier (lam S : ℝ) (q : ℝ → ℝ) (p : ℝ) : ℝ :=
  p*((1-p)-capSlack lam S (q p))
noncomputable def stationaryBarrierSlope (lam S : ℝ) (q : ℝ → ℝ) (p : ℝ) : ℝ :=
  1-2*p-capSlack lam S (q p)+p*(1-p)/(lam-q p)
noncomputable def stationaryBarrierCurvature (lam S p q : ℝ) : ℝ :=
  -2+(2-3*p)/(lam-q)+p*(1-p)^2/((lam-q)^3*capSlopeGap lam S q)

theorem stationaryBarrier_hasDerivAt {lam S p : ℝ} {q : ℝ → ℝ}
    (hq : HasDerivAt q ((1-p)/((lam-q p)*capSlopeGap lam S (q p))) p)
    (hql : q p ≠ lam) (hq1 : q p ≠ 1) (hgap : capSlopeGap lam S (q p) ≠ 0) :
    HasDerivAt (stationaryBarrier lam S q) (stationaryBarrierSlope lam S q p) p := by
  have hd := (hasDerivAt_id p).mul
    (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).sub ((capSlack_hasDerivAt lam S (q p) hq1).comp p hq))
  have hl : lam-q p ≠ 0 := sub_ne_zero.mpr (Ne.symm hql)
  convert! hd using 1 <;> first | rfl |
    (simp only [stationaryBarrierSlope,Pi.sub_apply,Function.comp_apply,id_eq]; field_simp; ring)

/-- The exact second derivative C.16 on the rational stationary branch. -/
theorem stationaryBarrierSlope_hasDerivAt {lam S p : ℝ} {q : ℝ → ℝ}
    (hq : HasDerivAt q ((1-p)/((lam-q p)*capSlopeGap lam S (q p))) p)
    (hql : q p ≠ lam) (hq1 : q p ≠ 1) (hgap : capSlopeGap lam S (q p) ≠ 0) :
    HasDerivAt (stationaryBarrierSlope lam S q) (stationaryBarrierCurvature lam S p (q p)) p := by
  have hl : lam-q p ≠ 0 := sub_ne_zero.mpr (Ne.symm hql)
  have hi := hasDerivAt_id p
  have hd := (((hasDerivAt_const p 1).sub (hi.const_mul 2)).sub
    ((capSlack_hasDerivAt lam S (q p) hq1).comp p hq)).add
    ((hi.mul ((hasDerivAt_const p 1).sub hi)).div ((hasDerivAt_const p lam).sub hq) hl)
  convert! hd using 1 <;> first | rfl |
    (simp only [stationaryBarrierCurvature,Pi.sub_apply,Pi.mul_apply,Function.comp_apply,id_eq]; field_simp; ring)


/-- Endpoint levels and a positive slope gap construct the whole stationary
branch, rather than postulating a differentiable maximizing-rank function. -/
theorem exists_rational_stationary_branch {lam S u v a b m : ℝ}
    (huv : u ≤ v) (hv1 : v < 1) (hvl : v < lam)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hm : 0 < m)
    (hcurv : ∀ r ∈ Icc u v,m ≤ 2*(lam-r)*capSlopeGap lam S r)
    (hleft : (1-a)^2 ≤ stationaryLevel lam S u)
    (hright : stationaryLevel lam S v ≤ (1-b)^2) :
    ∃ q : ℝ → ℝ,(∀ p ∈ Icc a b,q p ∈ Icc u v ∧
      stationaryLevel lam S (q p)=(1-p)^2) ∧
      LipschitzOnWith (2/⟨m,hm.le⟩ : ℝ≥0) q (Icc a b) ∧
      (∀ p ∈ Ioo a b,HasDerivAt q
        ((1-p)/((lam-q p)*capSlopeGap lam S (q p))) p) := by
  let F := fun r => -stationaryLevel lam S r
  let G := fun p : ℝ => -(1-p)^2
  have hFder (r : ℝ) (hr : r ∈ Icc u v) :
      HasDerivAt F (2*(lam-r)*capSlopeGap lam S r) r := by
    convert! (stationaryLevel_hasDerivAt lam S r (ne_of_lt (hr.2.trans_lt hv1))).neg using 1 <;>
      first | rfl | ring
  have hFc : ContinuousOn F (Icc u v) := fun r hr => (hFder r hr).continuousAt.continuousWithinAt
  have hgrowth : ∀ x ∈ Icc u v,∀ y ∈ Icc u v,x ≤ y → m*(y-x) ≤ F y-F x := by
    have hmono : MonotoneOn (fun r => F r-m*r) (Icc u v) := by
      have hd (r : ℝ) (hr : r ∈ Icc u v) :
          HasDerivAt (fun r => F r-m*r) (2*(lam-r)*capSlopeGap lam S r-m) r := by
        convert! (hFder r hr).sub ((hasDerivAt_id r).const_mul m) using 1 <;>
          first | rfl | simp only [mul_one,id_eq]
      apply monotoneOn_of_deriv_nonneg (convex_Icc u v)
        (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
        (fun r hr => (hd r (interior_subset hr)).differentiableAt.differentiableWithinAt)
      intro r hr
      rw [(hd r (interior_subset hr)).deriv]
      exact sub_nonneg.mpr (hcurv r (interior_subset hr))
    intro x hx y hy hxy
    have hh := hmono hx hy hxy
    dsimp only at hh
    nlinarith only [hh]
  have hGlip : LipschitzOnWith (2 : ℝ≥0) G (Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hx0 : 0 ≤ x := ha.trans hx.1
    have hx1 : x ≤ 1 := hx.2.trans hb
    have hy0 : 0 ≤ y := ha.trans hy.1
    have hy1 : y ≤ 1 := hy.2.trans hb
    have hbound : |2-x-y| ≤ 2 := abs_le.mpr ⟨by linarith,by linarith⟩
    change dist (G x) (G y) ≤ 2*dist x y
    rw [Real.dist_eq,Real.dist_eq]
    have he : G x-G y=(x-y)*(2-x-y) := by dsimp [G]; ring
    rw [he,abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hbound (abs_nonneg (x-y))]
  have hrange : ∀ p ∈ Icc a b,G p ∈ Icc (F u) (F v) := by
    intro p hp
    have hp1 : p ≤ 1 := hp.2.trans hb
    have ha1 : a ≤ 1 := hab.trans hb
    have hlow := sq_le_sq₀ (by linarith : 0 ≤ 1-p) (by linarith : 0 ≤ 1-a)
    have hhigh := sq_le_sq₀ (by linarith : 0 ≤ 1-b) (by linarith : 0 ≤ 1-p)
    have hs1 : (1-p)^2 ≤ (1-a)^2 := hlow.mpr (by linarith [hp.1])
    have hs2 : (1-b)^2 ≤ (1-p)^2 := hhigh.mpr (by linarith [hp.2])
    constructor <;> dsimp [F,G] <;> linarith
  obtain ⟨q,hq,hqlip⟩ := exists_lipschitz_implicit_curve huv hm hFc hgrowth hGlip hrange
  have hmatch : ∀ p ∈ Icc a b,q p ∈ Icc u v ∧ stationaryLevel lam S (q p)=(1-p)^2 := by
    intro p hp
    refine ⟨(hq p hp).1,?_⟩
    have hh := (hq p hp).2
    dsimp [F,G] at hh
    linarith
  refine ⟨q,hmatch,hqlip,?_⟩
  intro p hp
  have hr := (hmatch p ⟨hp.1.le,hp.2.le⟩).1
  have hgap : 0 < capSlopeGap lam S (q p) := by
    have hh := hcurv (q p) hr
    have hprod : 0 < 2*(lam-q p)*capSlopeGap lam S (q p) := hm.trans_le hh
    exact pos_of_mul_pos_right hprod (by linarith [hr.2])
  exact stationary_branch_hasDerivAt hp hqlip.continuousOn (fun p hp => (hmatch p hp).2)
    (hr.2.trans_lt hvl) (ne_of_lt (hr.2.trans_lt hv1)) hgap

end OptimalG.Variational
