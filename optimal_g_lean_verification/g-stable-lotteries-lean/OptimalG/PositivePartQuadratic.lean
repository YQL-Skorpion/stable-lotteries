import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

/-! Algebraic envelopes for a concave split quadratic and its positive-part
maximum. These lemmas replace numerical subdivision in the split variable. -/
namespace OptimalG
open Set

theorem concave_quadratic_le_positive_square {L K q : ℝ}
    (hK : 0<K) (hq : 0≤q) :
    L*q-K*q^2/2≤(max L 0)^2/(2*K) := by
  by_cases hL : 0≤L
  · rw [max_eq_left hL]
    apply (le_div_iff₀ (by positivity : 0<2*K)).mpr
    nlinarith only [sq_nonneg (K*q-L)]
  · rw [max_eq_right (le_of_not_ge hL)]
    have h1 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hL) hq
    have h2 := mul_nonneg hK.le (sq_nonneg q)
    simp only [zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_div]
    linarith only [h1,h2]

/-- Squaring the positive part of an affine function preserves convexity. -/
theorem convex_positive_affine_square (D E : ℝ) :
    ConvexOn ℝ univ (fun x : ℝ => (max (D+E*x) 0)^2) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  let u := max (D+E*x) 0
  let v := max (D+E*y) 0
  have hu : 0≤u := le_max_right _ _
  have hv : 0≤v := le_max_right _ _
  have hmix0 : 0≤a*u+b*v := add_nonneg (mul_nonneg ha hu) (mul_nonneg hb hv)
  have hmix : max (D+E*(a*x+b*y)) 0≤a*u+b*v := by
    apply max_le _ hmix0
    have h1 := mul_le_mul_of_nonneg_left (le_max_left (D+E*x) 0) ha
    have h2 := mul_le_mul_of_nonneg_left (le_max_left (D+E*y) 0) hb
    have hid : D+E*(a*x+b*y)=a*(D+E*x)+b*(D+E*y) := by
      have hbval : b=1-a := by linarith only [hab]
      rw [hbval]
      ring
    rw [hid]
    exact add_le_add h1 h2
  have hs := pow_le_pow_left₀ (le_max_right (D+E*(a*x+b*y)) 0) hmix 2
  have hvar := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (u-v))
  have hbval : b=1-a := by linarith only [hab]
  have hid : a*u^2+b*v^2-(a*u+b*v)^2=a*b*(u-v)^2 := by rw [hbval]; ring
  change (max (D+E*(a*x+b*y)) 0)^2≤a*u^2+b*v^2
  nlinarith only [hs,hvar,hid]

/-- A positive-part quadratic plus any affine term is controlled by its
endpoint values throughout the interval. -/
theorem positive_affine_square_le_endpoints {A B C D E a b : ℝ}
    (hC : 0≤C)
    (ha : A+B*a+C*(max (D+E*a) 0)^2≤0)
    (hb : A+B*b+C*(max (D+E*b) 0)^2≤0) :
    ∀ x∈Icc a b,A+B*x+C*(max (D+E*x) 0)^2≤0 := by
  have hquad := (convex_positive_affine_square D E).smul hC
  have hlin : ConvexOn ℝ (univ : Set ℝ) (fun x => A+B*x) := by
    refine ⟨convex_univ,?_⟩
    intro x _ y _ u v _ _ huv
    simp only [smul_eq_mul]
    have hvval : v=1-u := by linarith only [huv]
    have he : A+B*(u*x+v*y)=u*(A+B*x)+v*(A+B*y) := by rw [hvval]; ring
    exact he.le
  have hc := hlin.add hquad
  intro x hx
  have hh := hc.le_max_of_mem_Icc (mem_univ a) (mem_univ b) hx
  change A+B*x+C*(max (D+E*x) 0)^2≤max (A+B*a+C*(max (D+E*a) 0)^2)
    (A+B*b+C*(max (D+E*b) 0)^2) at hh
  exact hh.trans (max_le ha hb)

end OptimalG
