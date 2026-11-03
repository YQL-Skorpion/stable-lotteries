import OptimalG.Certificates.ExtendedTailExpressions
import OptimalG.ExtendedSelectedAnalytic

namespace OptimalG
open Set Variational Certificates.ExtendedScalarExpressions
open Certificates.ExtendedSelectedExpressions (headLinear)
open Certificates.ExtendedTailExpressions

noncomputable def extendedTailEnvelope (phi : ℝ→ℝ) (lam S p t z Y H q : ℝ) : ℝ :=
  denominator lam S p t*(z+q-lam)+betaNumerator lam p t*
    (curvePrimitive phi (z-p+q)-tailPrimitive (539/625) Y H z-curvePrimitive phi q)+
    etaNumerator lam S p t*tailScore (539/625) Y H z

theorem extendedTailEnvelope_le_slacks {phi : ℝ→ℝ} {lam S p t z Y H q su eu : ℝ}
    (hJ : 0≤betaNumerator lam p t)
    (hslack : quadratic lam q-curvePrimitive phi q≤su)
    (hremaining : curvePrimitive phi (z-p+q)-quadratic lam (z-p+q)+S≤eu) :
    extendedTailEnvelope phi lam S p t z Y H q≤base lam S p t z Y H+
      q*(denominator lam S p t-betaNumerator lam p t*(z-p))+betaNumerator lam p t*(su+eu) := by
  have hh := mul_le_mul_of_nonneg_left (add_le_add hslack hremaining) hJ
  unfold extendedTailEnvelope base quadratic at *
  nlinarith only [hh]

theorem extended_tail_head_inactive {lam S p t z Y H q : ℝ}
    (hJ : 0≤betaNumerator lam p t) (hs : 0≤1+Certificates.SmallMassExpressions.slope lam S)
    (hq : 0≤q) (hz : 7/8≤z)
    (hlin : headLinear lam S p t (7/8)≤0) (hb : base lam S p t z Y H≤0) :
    headCore lam S p t z Y H q≤0 := by
  have hm := mul_nonneg hJ (sub_nonneg.mpr hz)
  have hl : headLinear lam S p t z≤0 := by
    unfold headLinear at *
    nlinarith only [hm,hlin]
  have ha := mul_nonpos_of_nonneg_of_nonpos hq hl
  have hc := mul_nonneg (mul_nonneg hJ hs) (sq_nonneg q)
  unfold headCore
  linarith only [ha,hc,hb]

theorem extended_tail_high_le_endpoints {lam S p t z Y H a b : ℝ}
    (ha : highCore lam S p t z Y H a≤0) (hb : highCore lam S p t z Y H b≤0) :
    ∀ q∈Icc a b,highCore lam S p t z Y H q≤0 := by
  have he (q : ℝ) : highCore lam S p t z Y H q=
      (base lam S p t z Y H+betaNumerator lam p t*S)+
      (denominator lam S p t-betaNumerator lam p t*(z-p))*q+
      (0:ℝ)*(max ((0:ℝ)+0*q) 0)^2 := by unfold highCore; ring
  rw [he a] at ha
  rw [he b] at hb
  intro q hq
  rw [he q]
  exact positive_affine_square_le_endpoints (by norm_num : (0:ℝ)≤0) ha hb q hq

theorem extended_tail_cap_le_endpoints {lam S p t z Y H a b : ℝ}
    (hJ : 0≤betaNumerator lam p t) (hab : a≤b) (harg : z-p+b<1)
    (hcap : ∀ u∈Icc a b,∀ v∈Icc a b,u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤
        capScore lam S (z-p+v)-capScore lam S (z-p+u))
    (ha : capCore lam S p t z Y H a≤0) (hb : capCore lam S p t z Y H b≤0) :
    ∀ q∈Icc a b,capCore lam S p t z Y H q≤0 := by
  let A := base lam S p t z Y H+betaNumerator lam p t*(S-quadratic lam (z-p))
  have he (q : ℝ) : capCore lam S p t z Y H q=
      capHeadEnvelope lam S (z-p) (Certificates.SmallMassExpressions.initial lam S)
        (Certificates.SmallMassExpressions.slope lam S) A (denominator lam S p t)
        (betaNumerator lam p t) q := by
    dsimp [A,capCore,headCore,headLinear,capHeadEnvelope,quadratic]
    ring
  rw [he a] at ha
  rw [he b] at hb
  intro q hq
  rw [he q]
  exact capHeadEnvelope_le_endpoints hJ hab harg hcap ha hb q hq

end OptimalG
