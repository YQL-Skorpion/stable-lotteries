import OptimalG.Certificates.CubicProfile
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Order.OrderClosed

/-! Gluing the checked polynomial pieces into a differentiable primitive. -/

namespace OptimalG.Certificates

open Set Filter
open scoped Topology

theorem hasDerivAt_glue_le (a : ℝ) (f g df dg : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (df x) x) (hg : ∀ x, HasDerivAt g (dg x) x)
    (hv : f a=g a) (hd : df a=dg a) (x : ℝ) :
    HasDerivAt (fun t => if t≤a then f t else g t) (if x≤a then df x else dg x) x := by
  rcases lt_trichotomy x a with hx | heq | hx
  · rw [if_pos (le_of_lt hx)]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with t ht
    exact if_pos (le_of_lt ht)
  · subst x
    rw [if_pos le_rfl]
    have hl : HasDerivWithinAt (fun t => if t≤a then f t else g t) (df a) (Iic a) a :=
      (hf a).hasDerivWithinAt.congr (fun t ht => if_pos ht) (if_pos le_rfl)
    have hr : HasDerivWithinAt (fun t => if t≤a then f t else g t) (df a) (Ioi a) a := by
      apply ((hg a).hasDerivWithinAt.congr_deriv hd.symm).congr
      · intro t ht
        exact if_neg (not_le_of_gt ht)
      · simpa only [if_pos le_rfl] using hv
    simpa only [Iic_union_Ioi,hasDerivWithinAt_univ] using hl.union hr
  · rw [if_neg (not_le_of_gt hx)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact if_neg (not_le_of_gt ht)

noncomputable def cubicScore (L : ℝ) : List CubicPiece → ℝ → ℝ
  | [], t => L-t
  | p::ps, t => if t≤p.hi then p.score (t-p.lo) else cubicScore L ps t

noncomputable def cubicPrimitive (L S : ℝ) : List CubicPiece → ℝ → ℝ
  | [], t => L*t-t^2/2-S
  | p::ps, t => if t≤p.hi then p.primitive (t-p.lo) else cubicPrimitive L S ps t

def CubicPiece.terminalCheck (p : CubicPiece) (L S : ℚ) : Bool := decide
  (p.scoreQ p.length=L-p.hi ∧ p.primitiveQ p.length=L*p.hi-p.hi^2/2-S)

def cubicAssemblyCheck (L S : ℚ) : List CubicPiece → Bool
  | [] => true
  | [p] => p.shapeCheck && p.terminalCheck L S
  | p::q::ps => p.shapeCheck && (p.joinCheck q && cubicAssemblyCheck L S (q::ps))

theorem cubicAssemblyCheck_head {L S : ℚ} {p : CubicPiece} {ps : List CubicPiece}
    (hc : cubicAssemblyCheck L S (p::ps)=true) : p.shapeCheck=true := by
  cases ps <;> simp only [cubicAssemblyCheck,Bool.and_eq_true] at hc <;> exact hc.1

private theorem terminalCheck_sound {L S : ℚ} {p : CubicPiece}
    (h : p.terminalCheck L S=true) :
    p.score (p.length:ℝ)=(L:ℝ)-p.hi ∧
      p.primitive (p.length:ℝ)=(L:ℝ)*p.hi-(p.hi:ℝ)^2/2-S := by
  have hh : p.scoreQ p.length=L-p.hi ∧ p.primitiveQ p.length=L*p.hi-p.hi^2/2-S := by
    simpa only [CubicPiece.terminalCheck,decide_eq_true_eq] using h
  constructor
  · have he := congrArg (fun q:ℚ => (q:ℝ)) hh.1
    simpa using he
  · have he := congrArg (fun q:ℚ => (q:ℝ)) hh.2
    simpa using he

/-- The checker guarantees the derivative identity across every join, including
the join to the final quadratic tail. -/
theorem cubicAssemblyCheck_regular (L S : ℚ) (ps : List CubicPiece)
    (hc : cubicAssemblyCheck L S ps=true) :
    Continuous (cubicScore L ps) ∧
      ∀ t, HasDerivAt (cubicPrimitive L S ps) (cubicScore L ps t) t := by
  induction ps with
  | nil =>
    refine ⟨continuous_const.sub continuous_id, ?_⟩
    intro t
    have hd := (((hasDerivAt_id t).const_mul (L:ℝ)).sub
      (((hasDerivAt_id t).pow 2).div_const 2)).sub_const (S:ℝ)
    change HasDerivAt (cubicPrimitive L S []) ((L:ℝ)*1-(2*t^(2-1)*1)/2) t at hd
    have he : (L:ℝ)*1-(2*t^(2-1)*1)/2=cubicScore L [] t := by
      unfold cubicScore
      ring
    rwa [he] at hd
  | cons p ps ih =>
    have hpder (t : ℝ) : HasDerivAt (fun t => p.primitive (t-p.lo)) (p.score (t-p.lo)) t := by
      simpa only [id_eq,mul_one,Function.comp_def] using
        (p.primitive_hasDerivAt (t-p.lo)).comp t ((hasDerivAt_id t).sub_const (p.lo:ℝ))
    have htail : cubicAssemblyCheck L S ps=true := by
      cases ps with
      | nil => rfl
      | cons q qs =>
        have hh : p.shapeCheck=true ∧ p.joinCheck q=true ∧ cubicAssemblyCheck L S (q::qs)=true := by
          simpa only [cubicAssemblyCheck,Bool.and_eq_true] using hc
        exact hh.2.2
    have hjoins : p.primitive ((p.hi:ℝ)-p.lo)=cubicPrimitive L S ps p.hi ∧
        p.score ((p.hi:ℝ)-p.lo)=cubicScore L ps p.hi := by
      cases ps with
      | nil =>
        have hh : p.shapeCheck=true ∧ p.terminalCheck L S=true := by
          simpa only [cubicAssemblyCheck,Bool.and_eq_true] using hc
        have hs := terminalCheck_sound hh.2
        simpa [CubicPiece.length,cubicPrimitive,cubicScore] using hs.symm
      | cons q qs =>
        have hh : p.shapeCheck=true ∧ p.joinCheck q=true ∧ cubicAssemblyCheck L S (q::qs)=true := by
          simpa only [cubicAssemblyCheck,Bool.and_eq_true] using hc
        have hj := CubicPiece.joinCheck_sound hh.2.1
        have hq := cubicAssemblyCheck_head htail
        have hlen : (0:ℚ)<q.length := by
          have hh : 0<q.length ∧ -(101/10:ℚ)<q.curvatureQ 0 ∧ q.curvatureQ 0<0 ∧
              -(101/10:ℚ)<q.curvatureQ q.length ∧ q.curvatureQ q.length<0 ∧
              -(1:ℚ)<q.slopeQ q.length ∧ q.slopeQ 0 < -(1/10:ℚ) := by
            simpa only [CubicPiece.shapeCheck,decide_eq_true_eq] using hq
          exact hh.1
        have hhi : (p.hi:ℝ)≤q.hi := by
          have hlo : (q.lo:ℝ)<q.hi := by
            have hh : q.lo<q.hi := by unfold CubicPiece.length at hlen; linarith
            exact_mod_cast hh
          rw [hj.1]
          exact le_of_lt hlo
        simp only [cubicPrimitive,cubicScore,if_pos hhi]
        rw [hj.1,sub_self]
        constructor
        · simpa [CubicPiece.length,hj.1] using hj.2.2.2
        · simpa [CubicPiece.length,hj.1] using hj.2.1
    have hpc : Continuous (fun t : ℝ => p.score (t-p.lo)) :=
      (continuous_iff_continuousAt.mpr (fun t => (p.score_hasDerivAt t).continuousAt)).comp
        (continuous_id.sub continuous_const)
    have hscore : Continuous (cubicScore L (p::ps)) := by
      apply hpc.if_le (ih htail).1 continuous_id continuous_const
      intro t ht
      change t=(p.hi:ℝ) at ht
      rw [ht]
      exact hjoins.2
    refine ⟨hscore, ?_⟩
    intro t
    exact hasDerivAt_glue_le p.hi (fun t => p.primitive (t-p.lo)) (cubicPrimitive L S ps)
      (fun t => p.score (t-p.lo)) (cubicScore L ps) hpder (ih htail).2 hjoins.1 hjoins.2 t

theorem cubicAssemblyCheck_hasDerivAt (L S : ℚ) (ps : List CubicPiece)
    (hc : cubicAssemblyCheck L S ps=true) (t : ℝ) :
    HasDerivAt (cubicPrimitive L S ps) (cubicScore L ps t) t :=
  (cubicAssemblyCheck_regular L S ps hc).2 t

theorem cubicAssemblyCheck_continuousScore (L S : ℚ) (ps : List CubicPiece)
    (hc : cubicAssemblyCheck L S ps=true) : Continuous (cubicScore L ps) :=
  (cubicAssemblyCheck_regular L S ps hc).1

end OptimalG.Certificates
