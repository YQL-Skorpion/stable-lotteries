import OptimalG.MiddleRankConvexity
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Exact split-rank calculus for the two-class inequalities. -/
namespace OptimalG
open Set

noncomputable def binaryRatio (phi : ℝ → ℝ) (lam p q : ℝ) : ℝ :=
  (curvePrimitive phi (q+1-p)-curvePrimitive phi q)/(lam-q)

noncomputable def binaryStationaryNumerator (phi : ℝ → ℝ) (lam p q : ℝ) : ℝ :=
  (lam-q)*(phi (q+1-p)-phi q)+curvePrimitive phi (q+1-p)-curvePrimitive phi q

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem binaryRatio_hasDerivAt {p q : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hq : 0 < q) (hqp : q < p) (hql : q < lam) :
    HasDerivAt (binaryRatio phi lam p)
      (binaryStationaryNumerator phi lam p q/(lam-q)^2) q := by
  have hqa : q ∈ Ioo (0 : ℝ) 1 := ⟨hq,hqp.trans hp.2⟩
  have hqb : q+1-p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.2],by linarith⟩
  have hb := (h.primitive_hasDerivAt hqb).comp q
    (((hasDerivAt_id q).add_const 1).sub_const p)
  have ha := h.primitive_hasDerivAt hqa
  have hd := (hb.sub ha).div ((hasDerivAt_const q lam).sub (hasDerivAt_id q))
    (sub_ne_zero.mpr (ne_of_gt hql))
  convert hd using 1 <;> first | rfl | (simp only [binaryStationaryNumerator,Pi.sub_apply,Function.comp_apply,id_eq]; ring)

theorem binaryRatio_stationary {p q : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hq : 0 < q) (hqp : q < p) (hql : q < lam)
    (hmax : IsLocalMax (binaryRatio phi lam p) q) :
    binaryStationaryNumerator phi lam p q=0 := by
  have hz := hmax.hasDerivAt_eq_zero (h.binaryRatio_hasDerivAt hp hq hqp hql)
  exact (div_eq_zero_iff).mp hz |>.resolve_right (pow_ne_zero 2 (sub_ne_zero.mpr (ne_of_gt hql)))

/-- The stationary ratio equals a score difference, with no score derivative required. -/
theorem binaryRatio_eq_score_difference {p q : ℝ} (hql : q < lam)
    (hstationary : binaryStationaryNumerator phi lam p q=0) :
    binaryRatio phi lam p q=phi q-phi (q+1-p) := by
  apply (div_eq_iff (sub_ne_zero.mpr (ne_of_gt hql))).mpr
  unfold binaryStationaryNumerator at hstationary
  nlinarith only [hstationary]

/-- On the straight segment, an interior stationary ratio is h minus the low deficit. -/
theorem binaryRatio_eq_deficit {p q : ℝ} (hql : q < lam)
    (hstationary : binaryStationaryNumerator phi lam p q=0)
    (hline : phi (q+1-p)=lam-(q+1-p)) :
    binaryRatio phi lam p q=(1-p)-(lam-q-phi q) := by
  rw [h.binaryRatio_eq_score_difference hql hstationary,hline]
  ring

/-- Formula C.13 for the derivative of the stationary numerator. -/
theorem binaryStationaryNumerator_hasDerivAt {p q dq dr : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hq : 0 < q) (hqp : q < p)
    (hdq : HasDerivAt phi dq q) (hdr : HasDerivAt phi dr (q+1-p)) :
    HasDerivAt (binaryStationaryNumerator phi lam p) ((lam-q)*(dr-dq)) q := by
  have hqa : q ∈ Ioo (0 : ℝ) 1 := ⟨hq,hqp.trans hp.2⟩
  have hqb : q+1-p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.2],by linarith⟩
  have hi := ((hasDerivAt_id q).add_const 1).sub_const p
  have hd := ((((hasDerivAt_const q lam).sub (hasDerivAt_id q)).mul
    ((hdr.comp q hi).sub hdq)).add ((h.primitive_hasDerivAt hqb).comp q hi)).sub
      (h.primitive_hasDerivAt hqa)
  convert hd using 1 <;> first | rfl | (simp only [Pi.sub_apply,Pi.mul_apply,Pi.add_apply,Function.comp_apply,id_eq]; ring)

end VerifierCurve
end OptimalG
