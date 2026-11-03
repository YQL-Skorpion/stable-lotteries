import OptimalG.RationalStationaryCurve
import OptimalG.BinaryStationary
import OptimalG.BarrierComparison

/-! The affine-head stationary barrier in C.3 is an actual constructed
Lipschitz branch. Its first derivative is proved from its matching equation. -/
namespace OptimalG
open Set
open scoped NNReal

noncomputable def headStationaryConstant (lam S phi0 slope : ℝ) : ℝ :=
  2*lam*(lam-phi0)-2*S-(1+slope)*lam^2
noncomputable def headStationaryLevel (lam S phi0 slope q : ℝ) : ℝ :=
  (1+slope)*(lam-q)^2+headStationaryConstant lam S phi0 slope
noncomputable def headSlack (lam phi0 slope q : ℝ) : ℝ :=
  lam-q-(phi0+slope*q)
noncomputable def headStationaryBarrier (lam phi0 slope : ℝ) (q : ℝ → ℝ) (p : ℝ) : ℝ :=
  p*((1-p)-headSlack lam phi0 slope (q p))
noncomputable def headStationaryBarrierSlope (lam phi0 slope : ℝ) (q : ℝ → ℝ) (p : ℝ) : ℝ :=
  1-2*p-headSlack lam phi0 slope (q p)+p*(1-p)/(lam-q p)

theorem headStationaryLevel_hasDerivAt (lam S phi0 slope q : ℝ) :
    HasDerivAt (headStationaryLevel lam S phi0 slope) (-2*(lam-q)*(1+slope)) q := by
  convert! (((((hasDerivAt_const q lam).sub (hasDerivAt_id q)).pow 2).const_mul (1+slope)).add_const
    (headStationaryConstant lam S phi0 slope)) using 1 <;>
    first | rfl | (simp only [Pi.sub_apply,id_eq,zero_sub,Nat.cast_ofNat,Nat.reduceSub,pow_one]; ring)

theorem headStationary_branch_hasDerivAt {lam S phi0 slope a b p : ℝ} {q : ℝ → ℝ}
    (hp : p ∈ Ioo a b) (hq : ContinuousOn q (Icc a b))
    (hmatch : ∀ t ∈ Icc a b,headStationaryLevel lam S phi0 slope (q t)=(1-t)^2)
    (hql : q p<lam) (hs : 0<1+slope) :
    HasDerivAt q ((1-p)/((lam-q p)*(1+slope))) p := by
  have hdG := (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).pow 2)
  have hden : -2*(lam-q p)*(1+slope)≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (ne_of_gt hql))) hs.ne'
  have hd := implicit_curve_hasDerivAt hp hq hmatch
    (headStationaryLevel_hasDerivAt lam S phi0 slope (q p)) hdG hden
  convert! hd using 1 <;> first | rfl |
    ((try simp only [Pi.sub_apply,id_eq]) <;> field_simp <;> ring)

theorem headSlack_hasDerivAt (lam phi0 slope q : ℝ) :
    HasDerivAt (headSlack lam phi0 slope) (-(1+slope)) q := by
  convert! ((hasDerivAt_const q lam).sub (hasDerivAt_id q)).sub
    (((hasDerivAt_id q).const_mul slope).const_add phi0) using 1 <;>
    first | rfl | ring

theorem headStationaryBarrier_hasDerivAt {lam phi0 slope p : ℝ} {q : ℝ → ℝ}
    (hq : HasDerivAt q ((1-p)/((lam-q p)*(1+slope))) p)
    (hql : q p≠lam) (hs : 1+slope≠0) :
    HasDerivAt (headStationaryBarrier lam phi0 slope q)
      (headStationaryBarrierSlope lam phi0 slope q p) p := by
  have hd := (hasDerivAt_id p).mul
    (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).sub
      ((headSlack_hasDerivAt lam phi0 slope (q p)).comp p hq))
  have hl : lam-q p≠0 := sub_ne_zero.mpr hql.symm
  convert! hd using 1 <;> first | rfl |
    (simp only [headStationaryBarrierSlope,Pi.sub_apply,Function.comp_apply,id_eq]; field_simp <;> ring)

/-- Compact endpoint level tests construct every rank on the affine-head
stationary branch and supply its actual derivative. -/
theorem exists_head_stationary_branch {lam S phi0 slope u v a b : ℝ}
    (huv : u≤v) (hvl : v<lam) (hs : 0<1+slope)
    (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hleft : (1-a)^2≤headStationaryLevel lam S phi0 slope u)
    (hright : headStationaryLevel lam S phi0 slope v≤(1-b)^2) :
    ∃ q : ℝ → ℝ,∃ K : ℝ≥0,
      (∀ p ∈ Icc a b,q p ∈ Icc u v ∧ headStationaryLevel lam S phi0 slope (q p)=(1-p)^2) ∧
      LipschitzOnWith K q (Icc a b) ∧
      (∀ p ∈ Ioo a b,HasDerivAt q ((1-p)/((lam-q p)*(1+slope))) p) := by
  let F := fun r => -headStationaryLevel lam S phi0 slope r
  let G := fun p : ℝ => -(1-p)^2
  let m := 2*(lam-v)*(1+slope)
  have hm : 0<m := by dsimp [m]; positivity
  have hFc : ContinuousOn F (Icc u v) := by dsimp [F,headStationaryLevel]; fun_prop
  have hgrowth : ∀ x ∈ Icc u v,∀ y ∈ Icc u v,x≤y → m*(y-x)≤F y-F x := by
    intro x hx y hy hxy
    have hh := mul_le_mul_of_nonneg_right (show 2*(lam-v)≤2*lam-x-y by linarith only [hx.2,hy.2])
      (mul_nonneg hs.le (sub_nonneg.mpr hxy))
    dsimp [F,headStationaryLevel,m]
    nlinarith only [hh]
  have hGlip : LipschitzOnWith (2:ℝ≥0) G (Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hx0 := ha.trans hx.1
    have hx1 := hx.2.trans hb
    have hy0 := ha.trans hy.1
    have hy1 := hy.2.trans hb
    have hbound : |2-x-y|≤2 := abs_le.mpr ⟨by linarith,by linarith⟩
    change dist (G x) (G y)≤2*dist x y
    rw [Real.dist_eq,Real.dist_eq]
    have he : G x-G y=(x-y)*(2-x-y) := by dsimp [G]; ring
    rw [he,abs_mul]
    nlinarith only [mul_le_mul_of_nonneg_left hbound (abs_nonneg (x-y))]
  have hrange : ∀ p ∈ Icc a b,G p ∈ Icc (F u) (F v) := by
    intro p hp
    have hp1 := hp.2.trans hb
    have ha1 := hab.trans hb
    have hs1 : (1-p)^2≤(1-a)^2 := (sq_le_sq₀ (by linarith) (by linarith)).mpr (by linarith only [hp.1])
    have hs2 : (1-b)^2≤(1-p)^2 := (sq_le_sq₀ (by linarith) (by linarith)).mpr (by linarith only [hp.2])
    constructor <;> dsimp [F,G] <;> linarith only [hleft,hright,hs1,hs2]
  obtain ⟨q,hq,hqlip⟩ := exists_lipschitz_implicit_curve huv hm hFc hgrowth hGlip hrange
  have hmatch : ∀ p ∈ Icc a b,q p ∈ Icc u v ∧ headStationaryLevel lam S phi0 slope (q p)=(1-p)^2 := by
    intro p hp
    refine ⟨(hq p hp).1,?_⟩
    have hh := (hq p hp).2
    dsimp [F,G] at hh
    linarith only [hh]
  exact ⟨q,_,hmatch,hqlip,fun p hp => headStationary_branch_hasDerivAt hp hqlip.continuousOn
    (fun p hp => (hmatch p hp).2) ((hmatch p ⟨hp.1.le,hp.2.le⟩).1.2.trans_lt hvl) hs⟩

/-- On the actual affine head and straight middle, the constructed matching
rank is an actual zero of the binary stationary numerator. -/
theorem headStationary_actual_root {phi : ℝ → ℝ} {lam S phi0 slope p q : ℝ}
    (hheadJ : curvePrimitive phi q=phi0*q+slope*q^2/2)
    (hheadScore : phi q=phi0+slope*q)
    (hshiftJ : curvePrimitive phi (q+1-p)=Variational.quadratic lam (q+1-p)-S)
    (hshiftScore : phi (q+1-p)=lam-(q+1-p))
    (hmatch : headStationaryLevel lam S phi0 slope q=(1-p)^2) :
    binaryStationaryNumerator phi lam p q=0 := by
  unfold binaryStationaryNumerator
  rw [hheadJ,hheadScore,hshiftJ,hshiftScore]
  unfold headStationaryLevel headStationaryConstant at hmatch
  unfold Variational.quadratic
  nlinarith only [hmatch]

/-- Strict monotonicity identifies the final matching rank with the head endpoint. -/
theorem headStationaryLevel_injective_left {lam S phi0 slope q r : ℝ}
    (hq : q<lam) (hr : r<lam) (hs : 0<1+slope)
    (he : headStationaryLevel lam S phi0 slope q=headStationaryLevel lam S phi0 slope r) : q=r := by
  have heq : (lam-q)^2=(lam-r)^2 := by
    unfold headStationaryLevel at he
    nlinarith only [he,hs]
  have hh := (sq_eq_sq₀ (sub_pos.mpr hq).le (sub_pos.mpr hr).le).mp heq
  linarith only [hh]

end OptimalG
