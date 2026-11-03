import OptimalG.Certificates.ExtendedSelectedExpressions
import OptimalG.PositivePartQuadratic
import OptimalG.CapHeadConvexity

/-! Analytic elimination of the selected-high split and rank variables.
The numerical inputs are endpoints of explicit scalar expressions; these
lemmas prove the intervening continuum bounds. -/
namespace OptimalG
open Set Variational Certificates.ExtendedScalarExpressions
open Certificates.ExtendedLocalExpressions Certificates.ExtendedSelectedExpressions

 theorem extended_headCore_le_gain {lam S p t z e q : ℝ}
    (hD0 : 0≤etaNumerator lam S (9/25) t)
    (hJ : 0<betaNumerator lam p t)
    (hs : 0<1+Certificates.SmallMassExpressions.slope lam S) (hq : 0≤q) :
    headCore lam S p t z e q≤headGain lam S p t z e := by
  have hh := concave_quadratic_le_positive_square
    (L:=headLinear lam S p t z) (mul_pos hJ hs) hq
  have hm := mul_le_mul_of_nonneg_left hh hD0
  unfold headCore headGain
  have he : 2*(betaNumerator lam p t*(1+Certificates.SmallMassExpressions.slope lam S))=
      2*betaNumerator lam p t*(1+Certificates.SmallMassExpressions.slope lam S) := by ring
  rw [he] at hm
  convert! add_le_add_left hm ((p-9/25)*localCore lam S p t z e) using 1 <;> ring

 theorem extended_headGain_of_cleared {lam S p t z e : ℝ}
    (hp : 9/25≤p) (hJ : 0<betaNumerator lam p t)
    (hs : 0<1+Certificates.SmallMassExpressions.slope lam S)
    (hT : localCore lam S p t z e≤0)
    (hclear : headGainCleared lam S p t z e≤0) :
    headGain lam S p t z e≤0 := by
  by_cases hlin : 0≤headLinear lam S p t z
  · unfold headGain
    rw [max_eq_left hlin]
    have hden : 0<2*betaNumerator lam p t*(1+Certificates.SmallMassExpressions.slope lam S) := by positivity
    apply nonpos_of_mul_nonpos_left (b := 2*betaNumerator lam p t*(1+Certificates.SmallMassExpressions.slope lam S)) _ hden
    convert! hclear using 1 <;> unfold headGainCleared <;> field_simp [hden.ne'] <;> ring
  · unfold headGain
    rw [max_eq_right (le_of_not_ge hlin)]
    simp only [zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero,zero_div,add_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hp) hT

 theorem extended_headGain_of_inactive {lam S p t z e : ℝ}
    (hp : 9/25≤p) (hT : localCore lam S p t z e≤0)
    (hlin : headLinear lam S p t z≤0) : headGain lam S p t z e≤0 := by
  unfold headGain
  rw [max_eq_right hlin]
  simp only [zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero,zero_div,add_zero]
  exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hp) hT

/-- For fixed parameters and any permitted deficit, the head maximum is
convex in the high rank. Endpoint checks cover the full high-rank interval. -/
 theorem extended_headGain_le_endpoints {lam S p t e a b : ℝ}
    (hD0 : 0≤etaNumerator lam S (9/25) t)
    (hJ : 0<betaNumerator lam p t)
    (hs : 0<1+Certificates.SmallMassExpressions.slope lam S)
    (ha : headGain lam S p t a e≤0) (hb : headGain lam S p t b e≤0) :
    ∀ z∈Icc a b,headGain lam S p t z e≤0 := by
  let A := (p-9/25)*localCore lam S p t 0 e
  let B := (p-9/25)*(localCore lam S p t 1 e-localCore lam S p t 0 e)
  let C := etaNumerator lam S (9/25) t/
    (2*betaNumerator lam p t*(1+Certificates.SmallMassExpressions.slope lam S))
  let D := denominator lam S p t+betaNumerator lam p t*
    (lam+p-Certificates.SmallMassExpressions.initial lam S)
  let E := -betaNumerator lam p t
  have he (z : ℝ) : headGain lam S p t z e=A+B*z+C*(max (D+E*z) 0)^2 := by
    dsimp [A,B,C,D,E]
    have hlin : headLinear lam S p t z=denominator lam S p t+
        betaNumerator lam p t*(lam+p-Certificates.SmallMassExpressions.initial lam S)+
        (-betaNumerator lam p t)*z := by unfold headLinear; ring
    unfold headGain
    rw [hlin]
    unfold localCore
    ring
  have hC : 0≤C := div_nonneg hD0 (by positivity)
  rw [he a] at ha
  rw [he b] at hb
  intro z hz
  rw [he z]
  exact positive_affine_square_le_endpoints hC ha hb z hz

 theorem extended_highRankCore_le_endpoints {lam S p t z e a b : ℝ}
    (ha : highRankCore lam S p t z e a≤0) (hb : highRankCore lam S p t z e b≤0) :
    ∀ q∈Icc a b,highRankCore lam S p t z e q≤0 := by
  let A := (p-9/25)*localCore lam S p t z e+
    etaNumerator lam S (9/25) t*betaNumerator lam p t*S
  let B := etaNumerator lam S (9/25) t*(denominator lam S p t-betaNumerator lam p t*(z-p))
  have he (q : ℝ) : highRankCore lam S p t z e q=A+B*q+(0:ℝ)*(max ((0:ℝ)+0*q) 0)^2 := by
    dsimp [A,B,highRankCore]
    ring
  rw [he a] at ha
  rw [he b] at hb
  intro q hq
  rw [he q]
  exact positive_affine_square_le_endpoints (by norm_num : (0:ℝ)≤0) ha hb q hq

/-- The cap-shift envelope is convex in the split. The condition on its
slope is the established cap/head slope ordering of the actual curve. -/
 theorem extended_capCore_le_endpoints {lam S p t z e a b : ℝ}
    (hD0 : 0≤etaNumerator lam S (9/25) t) (hJ : 0≤betaNumerator lam p t)
    (hab : a≤b) (harg : z-p+b<1)
    (hcap : ∀ u∈Icc a b,∀ v∈Icc a b,u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤
        capScore lam S (z-p+v)-capScore lam S (z-p+u))
    (ha : capCore lam S p t z e a≤0) (hb : capCore lam S p t z e b≤0) :
    ∀ q∈Icc a b,capCore lam S p t z e q≤0 := by
  let A := (p-9/25)*localCore lam S p t z e+
    etaNumerator lam S (9/25) t*betaNumerator lam p t*(S-quadratic lam (z-p))
  let B := etaNumerator lam S (9/25) t*denominator lam S p t
  let K := etaNumerator lam S (9/25) t*betaNumerator lam p t
  have he (q : ℝ) : capCore lam S p t z e q=
      capHeadEnvelope lam S (z-p) (Certificates.SmallMassExpressions.initial lam S)
        (Certificates.SmallMassExpressions.slope lam S) A B K q := by
    dsimp [A,B,K,capCore,headCore,headLinear,capHeadEnvelope,quadratic]
    ring
  rw [he a] at ha
  rw [he b] at hb
  intro q hq
  rw [he q]
  exact capHeadEnvelope_le_endpoints (mul_nonneg hD0 hJ) hab harg hcap ha hb q hq

end OptimalG
