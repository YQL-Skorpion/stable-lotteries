import OptimalG.TailControlBox
import OptimalG.ExtendedHighReduction

/-! The local extended masses preserve their zero-split control through
the actual quadratic tail. The derivative-gap reduction then covers every
split rank. All remaining scalar inputs are explicit coefficient boxes. -/
namespace OptimalG
open Set Variational

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem local_tail_from_selected_endpoint {S p beta eta Y H : ℝ}
    (hL : lam ≤ 56233/100000) (hp : p ∈ Icc (9/25 : ℝ) (19/50))
    (hb : 0 ≤ beta) (he : 0 < eta)
    (htheta : 1/eta ≤ 81/100) (halpha : beta/eta ≤ 3)
    (hv : (309/50 : ℝ) ≤ tailBackwardSlope (7/8) Y H)
    (hk : tailBackwardCurvature (7/8) Y H ∈ Icc (0 : ℝ) (1273/100))
    (hscore : ∀ r ∈ Icc (7/8 : ℝ) 1, phi r = tailScore (7/8) Y H r)
    (hprimitive : ∀ r ∈ Icc (7/8 : ℝ) 1,
      curvePrimitive phi r = tailPrimitive (7/8) Y H r)
    (hline : ∀ r ∈ Icc (99/200 : ℝ) (16/25),
      curvePrimitive phi r = quadratic lam r - S)
    (hlow : ∀ u ∈ Icc (0 : ℝ) lam, phi 0 - u ≤ phi u)
    (hpL : p ≤ lam)
    (hgap : 1 ≤ beta * (phi 0 - lam + 391/500 - p))
    (hstart : 7/8 - lam + beta * packingK phi p 0 (7/8) + eta * phi (7/8) ≤ 0) :
    ∀ z ∈ Icc (7/8 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) p,
      z + q - lam + beta * packingK phi p q z + eta * phi z ≤ 0 := by
  have hshift (z : ℝ) (hz : z ∈ Icc (7/8 : ℝ) 1) :
      curvePrimitive phi (z-p) = quadratic lam (z-p) - S :=
    hline (z-p) ⟨by linarith only [hz.1, hp.2], by linarith only [hz.2, hp.1]⟩
  have hzero : curvePrimitive phi 0 = 0 := by simp [curvePrimitive]
  have hstart' : 7/8-lam+beta*(quadratic lam (7/8-p)-S-
      tailPrimitive (7/8) Y H (7/8))+eta*tailScore (7/8) Y H (7/8) ≤ 0 := by
    simpa only [packingK, add_zero, hshift (7/8) ⟨le_rfl, by norm_num⟩,
      hprimitive (7/8) ⟨le_rfl, by norm_num⟩, hscore (7/8) ⟨le_rfl, by norm_num⟩,
      hzero, sub_zero] using hstart
  have hgapStart : 0 ≤ tailControlGap (7/8) Y H lam S p (1/eta) (beta/eta) (7/8) := by
    apply nonneg_of_mul_nonneg_right (a := eta) _ he
    have hid : eta * tailControlGap (7/8) Y H lam S p (1/eta) (beta/eta) (7/8) =
        -(7/8-lam+beta*(quadratic lam (7/8-p)-S-tailPrimitive (7/8) Y H (7/8))+
          eta*tailScore (7/8) Y H (7/8)) := by
      unfold tailControlGap
      field_simp [he.ne'] <;> ring
    rw [hid]
    exact neg_nonneg.mpr hstart'
  have hslope := tailControlSlope_endpoints_box
    (show (7/8 : ℝ) ∈ Ico (849/1000 : ℝ) 1 by norm_num)
    hv hk.2 hL hp.2 htheta ⟨div_nonneg hb he.le, halpha⟩
  have hcontrol := tailControl_preserved (7/8) Y H lam S p (1/eta) (beta/eta)
    (by norm_num) hk.1 (div_nonneg hb he.le) hgapStart hslope.1 hslope.2
  intro z hz q hq
  have ht := mul_le_mul_of_nonneg_left (hcontrol z hz) he.le
  have hzeroSplit : z-lam+beta*packingK phi p 0 z+eta*phi z ≤ 0 := by
    rw [packingK, add_zero, hzero, sub_zero, hshift z hz, hprimitive z hz, hscore z hz]
    have hcancel : eta * (-(1/eta)*(z-lam)-beta/eta*
        (quadratic lam (z-p)-S-tailPrimitive (7/8) Y H z)) =
        -(z-lam)-beta*(quadratic lam (z-p)-S-tailPrimitive (7/8) Y H z) := by
      field_simp [he.ne'] <;> ring
    rw [hcancel] at ht
    linarith only [ht]
  have hg := hgap.trans (mul_le_mul_of_nonneg_left
    (show phi 0-lam+391/500-p ≤ phi 0-lam+z-p by linarith only [hz.1]) hb)
  have hsplit := h.testValue_le_zero_split hlow hq.1 hq.2 (hq.2.trans hpL)
    (by linarith only [hp.2, hz.1]) hz.2 hb hg
  linarith only [hzeroSplit, hsplit]

end VerifierCurve
end OptimalG
