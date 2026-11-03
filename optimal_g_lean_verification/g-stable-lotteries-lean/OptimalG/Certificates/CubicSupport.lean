import OptimalG.Certificates.CubicAssembly
import OptimalG.Certificates.CubicEvaluation

/-! Exact supporting-line inequalities for the cubic score chain. -/
namespace OptimalG.Certificates
open Set

namespace CubicPiece

theorem tangent_bound {p : CubicPiece} (hc : p.shapeCheck=true)
    {s t : ℝ} (hs : s∈Icc 0 (p.length:ℝ)) (ht : t∈Icc 0 (p.length:ℝ)) :
    p.score t≤p.score s+p.slope s*(t-s) := by
  have hcur : 2*p.curvature s+p.curvature t≤0 := by
    linarith [(shapeCheck_curvature hc hs).2,(shapeCheck_curvature hc ht).2]
  have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (t-s)) hcur
  unfold score slope curvature at *
  nlinarith only [hm]

theorem slope_antitone {p : CubicPiece} (hc : p.shapeCheck=true) :
    AntitoneOn p.slope (Icc 0 (p.length:ℝ)) := by
  intro s hs t ht hst
  have hcur : p.curvature s+p.curvature t≤0 := by
    linarith [(shapeCheck_curvature hc hs).2,(shapeCheck_curvature hc ht).2]
  have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hst) hcur
  unfold slope curvature at *
  nlinarith only [hm]

theorem shapeCheck_length_pos {p : CubicPiece} (hc : p.shapeCheck=true) : 0<p.length := by
  have hh : 0<p.length ∧ -(101/10:ℚ)<p.curvatureQ 0 ∧ p.curvatureQ 0<0 ∧
      -(101/10:ℚ)<p.curvatureQ p.length ∧ p.curvatureQ p.length<0 ∧
      -(1:ℚ)<p.slopeQ p.length ∧ p.slopeQ 0 < -(1/10:ℚ) := by
    simpa only [shapeCheck,decide_eq_true_eq] using hc
  exact hh.1

end CubicPiece

noncomputable def cubicSlope : List CubicPiece → ℝ → ℝ
  | [], _ => -1
  | p::ps, r => if r≤p.hi then p.slope (r-p.lo) else cubicSlope ps r

/-- No restriction is imposed on an empty tail; a nonempty tail starts at its
first exact knot. -/
def CubicStartsBefore (ps : List CubicPiece) (r : ℝ) : Prop :=
  match ps with
  | [] => True
  | p::_ => (p.lo:ℝ)≤r

theorem cubicAssemblyCheck_tail {L S : ℚ} {p : CubicPiece} {ps : List CubicPiece}
    (hc : cubicAssemblyCheck L S (p::ps)=true) : cubicAssemblyCheck L S ps=true := by
  cases ps with
  | nil => rfl
  | cons q qs =>
    simp only [cubicAssemblyCheck,Bool.and_eq_true] at hc
    exact hc.2.2

theorem cubicAssemblyCheck_tail_start {L S : ℚ} {p : CubicPiece} {ps : List CubicPiece}
    (hc : cubicAssemblyCheck L S (p::ps)=true) {r : ℝ} (hr : (p.hi:ℝ)≤r) :
    CubicStartsBefore ps r := by
  cases ps with
  | nil => trivial
  | cons q qs =>
    have hh : p.shapeCheck=true ∧ p.joinCheck q=true ∧ cubicAssemblyCheck L S (q::qs)=true := by
      simpa only [cubicAssemblyCheck,Bool.and_eq_true] using hc
    have hj := CubicPiece.joinCheck_sound hh.2.1
    change (q.lo:ℝ)≤r
    rwa [← hj.1]

/-- The score and the one-sided slope agree at interior joins; the final
quadratic tail may have a downward slope jump, which preserves support. -/
theorem cubicAssemblyCheck_support_join {L S : ℚ} {p : CubicPiece} {ps : List CubicPiece}
    (hc : cubicAssemblyCheck L S (p::ps)=true) :
    cubicScore L ps p.hi=p.score p.length ∧ cubicSlope ps p.hi≤p.slope p.length := by
  cases ps with
  | nil =>
    have hh : p.shapeCheck=true ∧ p.terminalCheck L S=true := by
      simpa only [cubicAssemblyCheck,Bool.and_eq_true] using hc
    have ht : p.scoreQ p.length=L-p.hi ∧ p.primitiveQ p.length=L*p.hi-p.hi^2/2-S := by
      simpa only [CubicPiece.terminalCheck,decide_eq_true_eq] using hh.2
    have hl : (0:ℝ)≤p.length := by exact_mod_cast le_of_lt (CubicPiece.shapeCheck_length_pos hh.1)
    constructor
    · have h := congrArg (fun q:ℚ => (q:ℝ)) ht.1
      simpa [cubicScore] using h.symm
    · exact le_of_lt (CubicPiece.shapeCheck_slope hh.1 ⟨hl,le_rfl⟩).1
  | cons q qs =>
    have hh : p.shapeCheck=true ∧ p.joinCheck q=true ∧ cubicAssemblyCheck L S (q::qs)=true := by
      simpa only [cubicAssemblyCheck,Bool.and_eq_true] using hc
    have hj := CubicPiece.joinCheck_sound hh.2.1
    have hq := cubicAssemblyCheck_head hh.2.2
    have hl : q.lo≤q.hi := le_of_lt (sub_pos.mp (CubicPiece.shapeCheck_length_pos hq))
    have hl' : (q.lo:ℝ)≤q.hi := by exact_mod_cast hl
    rw [hj.1]
    simp only [cubicScore,cubicSlope,if_pos hl',sub_self]
    exact ⟨hj.2.1.symm,le_of_eq hj.2.2.1.symm⟩

/-- The tail slope never exceeds the slope at the previous join. -/
theorem cubicAssemblyCheck_slope_bound {L S : ℚ} {p : CubicPiece} {ps : List CubicPiece}
    (hc : cubicAssemblyCheck L S (p::ps)=true) {r : ℝ} (hr : (p.lo:ℝ)≤r) :
    -1≤cubicSlope (p::ps) r ∧ cubicSlope (p::ps) r≤p.slope 0 := by
  induction ps generalizing p with
  | nil =>
    have hp := cubicAssemblyCheck_head hc
    have hl : (0:ℝ)≤p.length := by exact_mod_cast le_of_lt (CubicPiece.shapeCheck_length_pos hp)
    by_cases hh : r≤p.hi
    · have ht : r-p.lo∈Icc 0 (p.length:ℝ) := by
        norm_num [CubicPiece.length]
        constructor <;> linarith
      rw [cubicSlope,if_pos hh]
      exact ⟨le_of_lt (CubicPiece.shapeCheck_slope hp ht).1,
        CubicPiece.slope_antitone hp ⟨le_rfl,hl⟩ ht ht.1⟩
    · rw [cubicSlope,if_neg hh,cubicSlope]
      exact ⟨le_rfl,le_of_lt (CubicPiece.shapeCheck_slope hp ⟨le_rfl,hl⟩).1⟩
  | cons q qs ih =>
    have hh : p.shapeCheck=true ∧ p.joinCheck q=true ∧ cubicAssemblyCheck L S (q::qs)=true := by
      simpa only [cubicAssemblyCheck,Bool.and_eq_true] using hc
    have hl : (0:ℝ)≤p.length := by exact_mod_cast le_of_lt (CubicPiece.shapeCheck_length_pos hh.1)
    by_cases ht : r≤p.hi
    · have ht' : r-p.lo∈Icc 0 (p.length:ℝ) := by
        norm_num [CubicPiece.length]
        constructor <;> linarith
      rw [cubicSlope,if_pos ht]
      exact ⟨le_of_lt (CubicPiece.shapeCheck_slope hh.1 ht').1,
        CubicPiece.slope_antitone hh.1 ⟨le_rfl,hl⟩ ht' ht'.1⟩
    · have hj := CubicPiece.joinCheck_sound hh.2.1
      have hqr : (q.lo:ℝ)≤r := by rw [← hj.1]; exact le_of_lt (lt_of_not_ge ht)
      have hq := ih hh.2.2 hqr
      rw [cubicSlope,if_neg ht]
      refine ⟨hq.1,hq.2.trans ?_⟩
      rw [← hj.2.2.1]
      exact CubicPiece.slope_antitone hh.1 ⟨le_rfl,hl⟩ ⟨hl,le_rfl⟩ hl

theorem cubicAssemblyCheck_tail_slope_bound {L S : ℚ} {p : CubicPiece} {ps : List CubicPiece}
    (hc : cubicAssemblyCheck L S (p::ps)=true) {r : ℝ} (hr : (p.hi:ℝ)≤r) :
    cubicSlope ps r≤p.slope p.length := by
  cases ps with
  | nil => exact (cubicAssemblyCheck_support_join hc).2
  | cons q qs =>
    have hh : p.shapeCheck=true ∧ p.joinCheck q=true ∧ cubicAssemblyCheck L S (q::qs)=true := by
      simpa only [cubicAssemblyCheck,Bool.and_eq_true] using hc
    have hj := CubicPiece.joinCheck_sound hh.2.1
    have hqr : (q.lo:ℝ)≤r := by rwa [← hj.1]
    have hb := (cubicAssemblyCheck_slope_bound hh.2.2 hqr).2
    exact hb.trans (le_of_eq hj.2.2.1.symm)

/-- Every one-sided slope in the chain gives a global upper support. This
includes every internal join and the downward slope jump to the final tail. -/
theorem cubicAssemblyCheck_support {L S : ℚ} {ps : List CubicPiece}
    (hc : cubicAssemblyCheck L S ps=true) {r s : ℝ}
    (hr : CubicStartsBefore ps r) (hs : CubicStartsBefore ps s) :
    cubicScore L ps s≤cubicScore L ps r+cubicSlope ps r*(s-r) := by
  induction ps generalizing r s with
  | nil => simp only [cubicScore,cubicSlope]; ring_nf; exact le_rfl
  | cons p ps ih =>
    change (p.lo:ℝ)≤r at hr
    change (p.lo:ℝ)≤s at hs
    have hp := cubicAssemblyCheck_head hc
    have ht := cubicAssemblyCheck_tail hc
    have hl : (0:ℝ)≤p.length := by exact_mod_cast le_of_lt (CubicPiece.shapeCheck_length_pos hp)
    have hlen : (p.length:ℝ)=(p.hi:ℝ)-p.lo := by simp [CubicPiece.length]
    have hjoin := cubicAssemblyCheck_support_join hc
    have hstart : CubicStartsBefore ps (p.hi:ℝ) := cubicAssemblyCheck_tail_start hc le_rfl
    by_cases hrr : r≤p.hi
    · have hr' : r-p.lo∈Icc 0 (p.length:ℝ) := by rw [hlen]; constructor <;> linarith
      by_cases hss : s≤p.hi
      · have hs' : s-p.lo∈Icc 0 (p.length:ℝ) := by rw [hlen]; constructor <;> linarith
        have hlocal := CubicPiece.tangent_bound hp hr' hs'
        simp only [cubicScore,cubicSlope,if_pos hrr,if_pos hss]
        convert hlocal using 1 <;> ring
      · have hshi : (p.hi:ℝ)≤s := le_of_lt (lt_of_not_ge hss)
        have htail := ih ht hstart (cubicAssemblyCheck_tail_start hc hshi)
        have hslope := hjoin.2.trans (CubicPiece.slope_antitone hp hr' ⟨hl,le_rfl⟩ hr'.2)
        have hmul := mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr hshi)
        have hlocal := CubicPiece.tangent_bound hp hr' ⟨hl,le_rfl⟩
        rw [hjoin.1] at htail
        simp only [cubicScore,cubicSlope,if_pos hrr,if_neg hss]
        simp only [hlen] at hlocal htail hmul
        nlinarith only [htail,hmul,hlocal]
    · have hrhi : (p.hi:ℝ)≤r := le_of_lt (lt_of_not_ge hrr)
      by_cases hss : s≤p.hi
      · have hs' : s-p.lo∈Icc 0 (p.length:ℝ) := by rw [hlen]; constructor <;> linarith
        have htail := ih ht (cubicAssemblyCheck_tail_start hc hrhi) hstart
        have hslope := cubicAssemblyCheck_tail_slope_bound hc hrhi
        have hmul := mul_le_mul_of_nonpos_right hslope (sub_nonpos.mpr hss)
        have hlocal := CubicPiece.tangent_bound hp ⟨hl,le_rfl⟩ hs'
        rw [hjoin.1] at htail
        simp only [cubicScore,cubicSlope,if_neg hrr,if_pos hss]
        simp only [hlen] at hlocal htail hmul
        nlinarith only [htail,hmul,hlocal]
      · simp only [cubicScore,cubicSlope,if_neg hrr,if_neg hss]
        exact ih ht (cubicAssemblyCheck_tail_start hc hrhi)
          (cubicAssemblyCheck_tail_start hc (le_of_lt (lt_of_not_ge hss)))

end OptimalG.Certificates
