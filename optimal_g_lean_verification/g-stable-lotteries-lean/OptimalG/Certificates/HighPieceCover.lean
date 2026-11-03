import OptimalG.Certificates.CubicLookup

/-! Standalone closed-cell coverage and evaluation for a checked cubic trajectory. -/
namespace OptimalG.Certificates.HighPieceCover
open Set

theorem tail_checked {L S : ℚ} {p : CubicPiece} {ps : List CubicPiece}
    (hc : trajectoryCheck L S (p::ps)=true) : trajectoryCheck L S ps=true := by
  cases ps with
  | nil => rfl
  | cons q qs => exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).2).2

theorem head_le_member {L S : ℚ} {p : CubicPiece} {ps : List CubicPiece}
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
      have ht := tail_checked hc
      have hlen : 0<p.length := of_decide_eq_true (trajectoryCheck_head hc)
      have hlo : p.lo<p.hi := by unfold CubicPiece.length at hlen;linarith
      exact hlo.le.trans (by simpa only [hj.1] using ih ht hq)

theorem member_lookup {L S : ℚ} {ps : List CubicPiece}
    (hc : trajectoryCheck L S ps=true) {p : CubicPiece} (hp : p∈ps) :
    cubicLookupCheck p ps=true := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    by_cases he : p=q
    · simp only [cubicLookupCheck,if_pos he]
    · have hmem : p∈qs := (List.mem_cons.mp hp).resolve_left he
      have ht := tail_checked hc
      have hlookup := ih ht hmem
      have horder : q.hi≤p.lo := by
        cases qs with
        | nil => simp at hmem
        | cons r rs =>
          have hj := trajectoryJoinCheck_sound
            (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).2).1
          rw [hj.1]
          exact head_le_member ht hmem
      simp only [cubicLookupCheck,if_neg he,decide_eq_true horder,hlookup,Bool.true_and]


theorem member_length_pos {L S : ℚ} {ps : List CubicPiece}
    (hc : trajectoryCheck L S ps=true) {p : CubicPiece} (hp : p∈ps) : p.lo<p.hi := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · have h := of_decide_eq_true (trajectoryCheck_head hc)
      simpa only [CubicPiece.length,sub_pos] using h
    · exact ih (tail_checked hc) hp

theorem cover_from_head {L S : ℚ} {p last : CubicPiece} {ps : List CubicPiece}
    (hc : trajectoryCheck L S (p::ps)=true) (hlast : last∈p::ps)
    {r : ℝ} (hr : (p.lo:ℝ)≤r ∧ r≤(last.hi:ℝ)) :
    ∃ q∈p::ps,r∈Icc (q.lo:ℝ) q.hi := by
  induction ps generalizing p with
  | nil =>
    have he : last=p := List.mem_singleton.mp hlast
    exact ⟨p,List.mem_cons_self,by simpa only [he,mem_Icc] using hr⟩
  | cons q qs ih =>
    by_cases hhi : r≤(p.hi:ℝ)
    · exact ⟨p,List.mem_cons_self,hr.1,hhi⟩
    · have hrest : last∈q::qs := by
        rcases List.mem_cons.mp hlast with he | hm
        · exact False.elim (hhi (by simpa only [he,mem_Icc] using hr.2))
        · exact hm
      have hj := trajectoryJoinCheck_sound
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).2).1
      have hl : (q.lo:ℝ)≤r := by
        have he : (p.hi:ℝ)=q.lo := by exact_mod_cast hj.1
        exact he ▸ (lt_of_not_ge hhi).le
      obtain ⟨v,hv,hrv⟩ := ih (tail_checked hc) hrest ⟨hl,hr.2⟩
      exact ⟨v,List.mem_cons_of_mem p hv,hrv⟩

/-- Any two member endpoints suffice; taking the first and last pieces gives
coverage of the entire advertised trajectory interval. -/
theorem cover {L S : ℚ} {ps : List CubicPiece} {first last : CubicPiece}
    (hc : trajectoryCheck L S ps=true) (hfirst : first∈ps) (hlast : last∈ps)
    {r : ℝ} (hr : (first.lo:ℝ)≤r ∧ r≤(last.hi:ℝ)) :
    ∃ q∈ps,r∈Icc (q.lo:ℝ) q.hi := by
  cases ps with
  | nil => simp at hfirst
  | cons p ps =>
    have hl : (p.lo:ℝ)≤first.lo := by exact_mod_cast head_le_member hc hfirst
    exact cover_from_head hc hlast ⟨hl.trans hr.1,hr.2⟩

theorem values {L S : ℚ} {ps : List CubicPiece} {first last : CubicPiece}
    (hc : trajectoryCheck L S ps=true) (hfirst : first∈ps) (hlast : last∈ps)
    {r : ℝ} (hr : (first.lo:ℝ)≤r ∧ r≤(last.hi:ℝ)) :
    ∃ q∈ps,r∈Icc (q.lo:ℝ) q.hi ∧
      cubicScore L ps r=q.score (r-q.lo) ∧
      cubicPrimitive L S ps r=q.primitive (r-q.lo) := by
  obtain ⟨q,hq,hrq⟩ := cover hc hfirst hlast hr
  have hcont : Continuous (cubicPrimitive L S ps) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (trajectoryCheck_hasDerivAt L S ps hc t).continuousAt)
  have hh := cubicLookupCheck_closed_values (member_lookup hc hq)
    (member_length_pos hc hq) (L:ℝ) (S:ℝ)
    (trajectoryCheck_continuousScore L S ps hc) hcont hrq
  exact ⟨q,hq,hrq,hh⟩

end OptimalG.Certificates.HighPieceCover
