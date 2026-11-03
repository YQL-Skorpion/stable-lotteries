import OptimalG.Certificates.Interval
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Exact cubic-score/quartic-primitive data and local shape checks. -/

namespace OptimalG.Certificates

structure CubicPiece where
  lo : ℚ
  hi : ℚ
  a0 : ℚ
  a1 : ℚ
  a2 : ℚ
  a3 : ℚ
  f0 : ℚ
  deriving DecidableEq, Repr

namespace CubicPiece

def length (p : CubicPiece) : ℚ := p.hi-p.lo
def scoreQ (p : CubicPiece) (t : ℚ) : ℚ := p.a0+p.a1*t+p.a2*t^2+p.a3*t^3
def slopeQ (p : CubicPiece) (t : ℚ) : ℚ := p.a1+2*p.a2*t+3*p.a3*t^2
def curvatureQ (p : CubicPiece) (t : ℚ) : ℚ := 2*p.a2+6*p.a3*t
def primitiveQ (p : CubicPiece) (t : ℚ) : ℚ :=
  p.f0+p.a0*t+p.a1/2*t^2+p.a2/3*t^3+p.a3/4*t^4

noncomputable def score (p : CubicPiece) (t : ℝ) : ℝ :=
  p.a0+p.a1*t+p.a2*t^2+p.a3*t^3
noncomputable def slope (p : CubicPiece) (t : ℝ) : ℝ := p.a1+2*p.a2*t+3*p.a3*t^2
noncomputable def curvature (p : CubicPiece) (t : ℝ) : ℝ := 2*p.a2+6*p.a3*t
noncomputable def primitive (p : CubicPiece) (t : ℝ) : ℝ :=
  p.f0+p.a0*t+p.a1/2*t^2+p.a2/3*t^3+p.a3/4*t^4

@[simp] theorem scoreQ_cast (p : CubicPiece) (t : ℚ) : (p.scoreQ t:ℝ) = p.score t := by
  simp [scoreQ,score]
@[simp] theorem slopeQ_cast (p : CubicPiece) (t : ℚ) : (p.slopeQ t:ℝ) = p.slope t := by
  simp [slopeQ,slope]
@[simp] theorem curvatureQ_cast (p : CubicPiece) (t : ℚ) : (p.curvatureQ t:ℝ) = p.curvature t := by
  simp [curvatureQ,curvature]
@[simp] theorem primitiveQ_cast (p : CubicPiece) (t : ℚ) : (p.primitiveQ t:ℝ) = p.primitive t := by
  simp [primitiveQ,primitive]

theorem score_hasDerivAt (p : CubicPiece) (t : ℝ) : HasDerivAt p.score (p.slope t) t := by
  have hd := (((hasDerivAt_const t (p.a0:ℝ)).add
    ((hasDerivAt_id t).const_mul (p.a1:ℝ))).add
    (((hasDerivAt_id t).pow 2).const_mul (p.a2:ℝ))).add
    (((hasDerivAt_id t).pow 3).const_mul (p.a3:ℝ))
  change HasDerivAt p.score
    (0+p.a1*1+p.a2*(2*t^(2-1)*1)+p.a3*(3*t^(3-1)*1)) t at hd
  have he : (0+(p.a1:ℝ)*1+p.a2*(2*t^(2-1)*1)+p.a3*(3*t^(3-1)*1)) = p.slope t := by
    unfold slope
    ring
  rwa [he] at hd

theorem primitive_hasDerivAt (p : CubicPiece) (t : ℝ) :
    HasDerivAt p.primitive (p.score t) t := by
  have hd := ((((hasDerivAt_const t (p.f0:ℝ)).add
    ((hasDerivAt_id t).const_mul (p.a0:ℝ))).add
    (((hasDerivAt_id t).pow 2).const_mul ((p.a1:ℝ)/2))).add
    (((hasDerivAt_id t).pow 3).const_mul ((p.a2:ℝ)/3))).add
    (((hasDerivAt_id t).pow 4).const_mul ((p.a3:ℝ)/4))
  change HasDerivAt p.primitive
    (0+p.a0*1+(p.a1:ℝ)/2*(2*t^(2-1)*1)+(p.a2:ℝ)/3*(3*t^(3-1)*1)+
      (p.a3:ℝ)/4*(4*t^(4-1)*1)) t at hd
  have he : (0+(p.a0:ℝ)*1+(p.a1:ℝ)/2*(2*t^(2-1)*1)+(p.a2:ℝ)/3*(3*t^(3-1)*1)+
      (p.a3:ℝ)/4*(4*t^(4-1)*1)) = p.score t := by
    unfold score
    ring
  rwa [he] at hd

def shapeCheck (p : CubicPiece) : Bool := decide
  (0 < p.length ∧ -(101/10:ℚ) < p.curvatureQ 0 ∧ p.curvatureQ 0 < 0 ∧
   -(101/10:ℚ) < p.curvatureQ p.length ∧ p.curvatureQ p.length < 0 ∧
   -(1:ℚ) < p.slopeQ p.length ∧ p.slopeQ 0 < -(1/10:ℚ))

/-- Linear curvature is enclosed throughout the interval by its endpoint bounds. -/
theorem shapeCheck_curvature {p : CubicPiece} (hc : p.shapeCheck = true)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (p.length:ℝ)) :
    -(10.1:ℝ) < p.curvature t ∧ p.curvature t < 0 := by
  have h : 0 < p.length ∧ -(101/10:ℚ) < p.curvatureQ 0 ∧ p.curvatureQ 0 < 0 ∧
      -(101/10:ℚ) < p.curvatureQ p.length ∧ p.curvatureQ p.length < 0 ∧
      -(1:ℚ) < p.slopeQ p.length ∧ p.slopeQ 0 < -(1/10:ℚ) := by
    simpa only [shapeCheck, decide_eq_true_eq] using hc
  have hlen : (0:ℝ) < p.length := by exact_mod_cast h.1
  have h0 : -(10.1:ℝ) < p.curvature 0 ∧ p.curvature 0 < 0 := by
    constructor
    · have hh : ((-(101/10:ℚ)):ℝ) < (p.curvatureQ 0:ℝ) := by exact_mod_cast h.2.1
      norm_num at hh ⊢
      exact hh
    · have hh : (p.curvatureQ 0:ℝ) < 0 := by exact_mod_cast h.2.2.1
      simpa using hh
  have h1 : -(10.1:ℝ) < p.curvature (p.length:ℝ) ∧ p.curvature (p.length:ℝ) < 0 := by
    constructor
    · have hh : ((-(101/10:ℚ)):ℝ) < (p.curvatureQ p.length:ℝ) := by exact_mod_cast h.2.2.2.1
      norm_num at hh ⊢
      exact hh
    · have hh : (p.curvatureQ p.length:ℝ) < 0 := by exact_mod_cast h.2.2.2.2.1
      simpa using hh
  have he : (p.length:ℝ)*p.curvature t =
      ((p.length:ℝ)-t)*p.curvature 0+t*p.curvature (p.length:ℝ) := by
    unfold curvature
    ring
  constructor
  · have hz : 0 < ((p.length:ℝ)-t)*(p.curvature 0+10.1)+t*(p.curvature (p.length:ℝ)+10.1) := by
      by_cases htz : t=0
      · subst t
        nlinarith [mul_pos hlen (show 0 < p.curvature 0+10.1 by linarith)]
      · have hp := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm htz)) (show 0 < p.curvature (p.length:ℝ)+10.1 by linarith)
        have hn := mul_nonneg (sub_nonneg.mpr ht.2) (show 0 ≤ p.curvature 0+10.1 by linarith)
        linarith
    nlinarith
  · have hz : ((p.length:ℝ)-t)*p.curvature 0+t*p.curvature (p.length:ℝ) < 0 := by
      by_cases htz : t=0
      · subst t
        nlinarith [mul_neg_of_pos_of_neg hlen h0.2]
      · have hp := mul_neg_of_pos_of_neg (lt_of_le_of_ne ht.1 (Ne.symm htz)) h1.2
        have hn := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) (le_of_lt h0.2)
        linarith
    nlinarith

theorem shapeCheck_slope {p : CubicPiece} (hc : p.shapeCheck = true)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (p.length:ℝ)) :
    -(1:ℝ) < p.slope t ∧ p.slope t < -(0.1:ℝ) := by
  have h : 0 < p.length ∧ -(101/10:ℚ) < p.curvatureQ 0 ∧ p.curvatureQ 0 < 0 ∧
      -(101/10:ℚ) < p.curvatureQ p.length ∧ p.curvatureQ p.length < 0 ∧
      -(1:ℚ) < p.slopeQ p.length ∧ p.slopeQ 0 < -(1/10:ℚ) := by
    simpa only [shapeCheck, decide_eq_true_eq] using hc
  have hlen : (0:ℝ) ≤ p.length := by exact_mod_cast le_of_lt h.1
  have hleft := (shapeCheck_curvature hc (t:=0) ⟨le_rfl,hlen⟩).2
  have hright := (shapeCheck_curvature hc (t:=(p.length:ℝ)) ⟨hlen,le_rfl⟩).2
  have hmid := (shapeCheck_curvature hc ht).2
  have hs0 : p.slope 0 < -(0.1:ℝ) := by
    have hh : (p.slopeQ 0:ℝ) < ((-(1/10:ℚ)):ℝ) := by exact_mod_cast h.2.2.2.2.2.2
    norm_num at hh ⊢
    exact hh
  have hs1 : -(1:ℝ) < p.slope (p.length:ℝ) := by
    have hh : -(1:ℝ) < (p.slopeQ p.length:ℝ) := by exact_mod_cast h.2.2.2.2.2.1
    simpa using hh
  have ha := mul_nonpos_of_nonneg_of_nonpos ht.1 (show p.curvature 0+p.curvature t ≤ 0 by linarith)
  have hb := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2)
    (show p.curvature t+p.curvature (p.length:ℝ) ≤ 0 by linarith)
  unfold slope curvature at *
  constructor <;> nlinarith

def joinCheck (p q : CubicPiece) : Bool := decide
  (p.hi=q.lo ∧ p.scoreQ p.length=q.a0 ∧ p.slopeQ p.length=q.a1 ∧ p.primitiveQ p.length=q.f0)

theorem joinCheck_sound {p q : CubicPiece} (h : p.joinCheck q = true) :
    p.hi=q.lo ∧ p.score p.length=q.score 0 ∧ p.slope p.length=q.slope 0 ∧
      p.primitive p.length=q.primitive 0 := by
  have hh : p.hi=q.lo ∧ p.scoreQ p.length=q.a0 ∧ p.slopeQ p.length=q.a1 ∧ p.primitiveQ p.length=q.f0 := by
    simpa only [joinCheck, decide_eq_true_eq] using h
  refine ⟨hh.1, ?_, ?_, ?_⟩
  · simpa [score] using congrArg (fun x:ℚ => (x:ℝ)) hh.2.1
  · simpa [slope] using congrArg (fun x:ℚ => (x:ℝ)) hh.2.2.1
  · simpa [primitive] using congrArg (fun x:ℚ => (x:ℝ)) hh.2.2.2

end CubicPiece

def cubicChainCheck : List CubicPiece → Bool
  | [] => true
  | [_] => true
  | p::q::ps => p.joinCheck q && cubicChainCheck (q::ps)

theorem cubic_all_shape_sound {pieces : List CubicPiece}
    (h : pieces.all CubicPiece.shapeCheck = true) {p : CubicPiece} (hp : p ∈ pieces)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (p.length:ℝ)) :
    (-(10.1:ℝ) < p.curvature t ∧ p.curvature t < 0) ∧
      (-(1:ℝ) < p.slope t ∧ p.slope t < -(0.1:ℝ)) := by
  have hc := List.all_eq_true.mp h p hp
  exact ⟨p.shapeCheck_curvature hc ht, p.shapeCheck_slope hc ht⟩

end OptimalG.Certificates
