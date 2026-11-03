import OptimalG.Certificates.ReferenceFlowAssembly

/-! A single checked C¹ trajectory also certifies the ordering needed by all
local lookups. No quadratic collection of numerical prefix checks is needed. -/
namespace OptimalG.Certificates
open Set MeasureTheory

theorem trajectoryCheck_tail {L S : ℚ} {p : CubicPiece} {ps : List CubicPiece}
    (hc : trajectoryCheck L S (p::ps)=true) : trajectoryCheck L S ps=true := by
  cases ps with
  | nil => rfl
  | cons q qs => exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).2).2

theorem trajectoryCheck_lower {L S : ℚ} {p : CubicPiece} {ps : List CubicPiece}
    (hc : trajectoryCheck L S (p::ps)=true) {q : CubicPiece} (hq : q∈p::ps) : p.lo≤q.lo := by
  induction ps generalizing p with
  | nil =>
    have he : q=p := List.mem_singleton.mp hq
    subst q
    exact le_rfl
  | cons r rs ih =>
    rcases List.mem_cons.mp hq with he | hq
    · subst q
      exact le_rfl
    · have hj := trajectoryJoinCheck_sound (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).2).1
      have ht := trajectoryCheck_tail hc
      have hlen : 0<p.length := of_decide_eq_true (trajectoryCheck_head hc)
      have hlo : p.lo<p.hi := by unfold CubicPiece.length at hlen;linarith
      exact hlo.le.trans (by simpa only [hj.1] using ih ht hq)

theorem trajectoryCheck_lookup {L S : ℚ} {ps : List CubicPiece}
    (hc : trajectoryCheck L S ps=true) {p : CubicPiece} (hp : p∈ps) :
    cubicLookupCheck p ps=true := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    by_cases he : p=q
    · simp only [cubicLookupCheck,if_pos he]
    · have hmem : p∈qs := (List.mem_cons.mp hp).resolve_left he
      have ht := trajectoryCheck_tail hc
      have hlookup := ih ht hmem
      have horder : q.hi≤p.lo := by
        cases qs with
        | nil => simp at hmem
        | cons r rs =>
          have hj := trajectoryJoinCheck_sound
            (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).2).1
          rw [hj.1]
          exact trajectoryCheck_lower ht hmem
      simp only [cubicLookupCheck,if_neg he,decide_eq_true horder,hlookup,Bool.true_and]

namespace Transport

theorem reference_flow_exists_enclosed_of_membership {a b L S : ℚ}
    {cells : List ReferenceFlowCell} {pieces : List CubicPiece}
    (pieceFor : ReferenceFlowCell→CubicPiece)
    (hcover : referenceFlowCoverCheck a b cells=true)
    (hlen : (b:ℝ)-a≤2/25)
    (hcurve : trajectoryCheck L S pieces=true)
    (hpolynomial : ∀ c∈cells,polynomialPieceCheck c.valuePolynomial
      c.segment.left.z c.segment.right.z (pieceFor c)=true)
    (hmembership : ∀ c∈cells,pieceFor c∈pieces)
    (halpha : ∀ c∈cells,∀ t∈Icc (0:ℝ) 1,|c.actualAlpha t|≤3)
    (hbeta : ∀ c∈cells,∀ t∈Icc (0:ℝ) 1,|c.actualBeta t|≤1000)
    (hresidual : ∀ c∈cells,∀ t∈Icc (0:ℝ) 1,
      |c.valuePolynomial.derivative.eval t/(c.length:ℝ)-
        c.actualAlpha t*c.valuePolynomial.eval t-c.actualBeta t|≤1/4000000000) :
    ∃ Z : ℝ→ℝ,
      Z a=cubicPrimitive L S pieces a ∧
      AbsolutelyContinuousOnInterval Z a b ∧
      (∀ᵐ z ∂volume.restrict (Icc (a:ℝ) b),deriv Z z=
        referenceField ReferenceFlowCell.actualAlpha cells z*Z z+
          referenceField ReferenceFlowCell.actualBeta cells z) ∧
      ∀ z∈Icc (a:ℝ) b,|Z z-cubicPrimitive L S pieces z|≤(z-a)/2500000000 :=
  reference_flow_exists_enclosed pieceFor hcover hlen hcurve hpolynomial
    (fun c hc => trajectoryCheck_lookup hcurve (hmembership c hc)) halpha hbeta hresidual

end Transport
end OptimalG.Certificates
