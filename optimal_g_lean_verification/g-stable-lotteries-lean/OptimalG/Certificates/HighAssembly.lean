import OptimalG.Certificates.CubicAssembly

/-! A general C¹ high-trajectory assembly checker, without low-profile shape restrictions. -/
namespace OptimalG.Certificates
open Set Filter
open scoped Topology

def trajectoryJoinCheck (p q : CubicPiece) : Bool := decide
  (p.hi=q.lo ∧ p.scoreQ p.length=q.a0 ∧ p.primitiveQ p.length=q.f0)

theorem trajectoryJoinCheck_sound {p q : CubicPiece} (h : trajectoryJoinCheck p q=true) :
    p.hi=q.lo ∧ p.score p.length=q.score 0 ∧ p.primitive p.length=q.primitive 0 := by
  have hh : p.hi=q.lo ∧ p.scoreQ p.length=q.a0 ∧ p.primitiveQ p.length=q.f0 := of_decide_eq_true h
  refine ⟨hh.1,?_,?_⟩
  · simpa [CubicPiece.score] using congrArg (fun q:ℚ => (q:ℝ)) hh.2.1
  · simpa [CubicPiece.primitive] using congrArg (fun q:ℚ => (q:ℝ)) hh.2.2

def trajectoryCheck (L S : ℚ) : List CubicPiece → Bool
  | [] => true
  | [p] => decide (0<p.length) && p.terminalCheck L S
  | p::q::ps => decide (0<p.length) && (trajectoryJoinCheck p q && trajectoryCheck L S (q::ps))

theorem trajectoryCheck_head {L S : ℚ} {p : CubicPiece} {ps : List CubicPiece}
    (hc : trajectoryCheck L S (p::ps)=true) : (decide (0<p.length))=true := by
  cases ps <;> simp only [trajectoryCheck,Bool.and_eq_true] at hc <;> exact hc.1

private theorem trajectoryTerminalCheck_sound {L S : ℚ} {p : CubicPiece}
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
theorem trajectoryCheck_regular (L S : ℚ) (ps : List CubicPiece)
    (hc : trajectoryCheck L S ps=true) :
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
    have htail : trajectoryCheck L S ps=true := by
      cases ps with
      | nil => rfl
      | cons q qs =>
        have hh : (decide (0<p.length))=true ∧ trajectoryJoinCheck p q=true ∧ trajectoryCheck L S (q::qs)=true := by
          simpa only [trajectoryCheck,Bool.and_eq_true] using hc
        exact hh.2.2
    have hjoins : p.primitive ((p.hi:ℝ)-p.lo)=cubicPrimitive L S ps p.hi ∧
        p.score ((p.hi:ℝ)-p.lo)=cubicScore L ps p.hi := by
      cases ps with
      | nil =>
        have hh : (decide (0<p.length))=true ∧ p.terminalCheck L S=true := by
          simpa only [trajectoryCheck,Bool.and_eq_true] using hc
        have hs := trajectoryTerminalCheck_sound hh.2
        simpa [CubicPiece.length,cubicPrimitive,cubicScore] using hs.symm
      | cons q qs =>
        have hh : (decide (0<p.length))=true ∧ trajectoryJoinCheck p q=true ∧ trajectoryCheck L S (q::qs)=true := by
          simpa only [trajectoryCheck,Bool.and_eq_true] using hc
        have hj := trajectoryJoinCheck_sound hh.2.1
        have hq := trajectoryCheck_head htail
        have hlen : (0:ℚ)<q.length := of_decide_eq_true hq
        have hhi : (p.hi:ℝ)≤q.hi := by
          have hlo : (q.lo:ℝ)<q.hi := by
            have hh : q.lo<q.hi := by unfold CubicPiece.length at hlen; linarith
            exact_mod_cast hh
          rw [hj.1]
          exact le_of_lt hlo
        simp only [cubicPrimitive,cubicScore,if_pos hhi]
        rw [hj.1,sub_self]
        constructor
        · simpa [CubicPiece.length,hj.1] using hj.2.2
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

theorem trajectoryCheck_hasDerivAt (L S : ℚ) (ps : List CubicPiece)
    (hc : trajectoryCheck L S ps=true) (t : ℝ) :
    HasDerivAt (cubicPrimitive L S ps) (cubicScore L ps t) t :=
  (trajectoryCheck_regular L S ps hc).2 t

theorem trajectoryCheck_continuousScore (L S : ℚ) (ps : List CubicPiece)
    (hc : trajectoryCheck L S ps=true) : Continuous (cubicScore L ps) :=
  (trajectoryCheck_regular L S ps hc).1

end OptimalG.Certificates
