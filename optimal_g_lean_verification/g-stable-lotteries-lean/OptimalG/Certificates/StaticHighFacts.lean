import OptimalG.Certificates.StaticHighData
import OptimalG.Certificates.HighPieceCover

namespace OptimalG.Certificates.StaticHighData
open Set

theorem primitive_continuous : Continuous primitive :=
  continuous_iff_continuousAt.mpr (fun r=>(primitive_hasDerivAt r).continuousAt)

theorem piece_values {p : CubicPiece} (hp : p∈pieces) {r : ℝ}
    (hr : r∈Icc (p.lo:ℝ) p.hi) :
    score r=p.score (r-p.lo) ∧ primitive r=p.primitive (r-p.lo) := by
  have hh := cubicLookupCheck_closed_values
    (HighPieceCover.member_lookup trajectory_checked hp)
    (HighPieceCover.member_length_pos trajectory_checked hp) 0 (-(1/2:ℚ))
    score_continuous primitive_continuous hr
  exact hh

theorem line_values {r : ℝ} (hr : r∈Icc (StaticLow.lam:ℝ) StaticHigh.departure) :
    score r=(StaticLow.lam:ℝ)-r ∧
      primitive r=quadratic StaticLow.lam r-StaticLow.slack := by
  have hp : piece0∈pieces := by simp only [pieces,List.mem_cons_self]
  have hmem : r∈Icc (piece0.lo:ℝ) piece0.hi := hr
  have hh := piece_values hp hmem
  rw [hh.1,hh.2]
  norm_num [piece0,CubicPiece.score,CubicPiece.primitive,StaticLow.lam,StaticLow.slack,quadratic]
  all_goals (try ring)
  all_goals simp

theorem initial_score : score StaticLow.lam=0 := by
  have hld : (StaticLow.lam:ℝ)≤StaticHigh.departure := by
    norm_num [StaticLow.lam,StaticHigh.departure]
  simpa using (line_values (r:=(StaticLow.lam:ℝ)) ⟨le_rfl,hld⟩).1

theorem initial_primitive : primitive StaticLow.lam=
    quadratic StaticLow.lam StaticLow.lam-StaticLow.slack := by
  have hld : (StaticLow.lam:ℝ)≤StaticHigh.departure := by
    norm_num [StaticLow.lam,StaticHigh.departure]
  exact (line_values ⟨le_rfl,hld⟩).2

theorem tail_values {r : ℝ} (hr : r∈Icc (StaticHigh.contact:ℝ) 1) :
    score r=tailScore StaticHigh.contact StaticHigh.contactValue StaticHigh.contactScore r ∧
      primitive r=tailPrimitive StaticHigh.contact StaticHigh.contactValue StaticHigh.contactScore r := by
  have hp : piece159∈pieces := by simp [pieces]
  have hmem : r∈Icc (piece159.lo:ℝ) piece159.hi := by convert! hr using 1 <;> norm_num [piece159,StaticHigh.contact]
  have hh := piece_values hp hmem
  rw [hh.1,hh.2]
  norm_num [piece159,CubicPiece.score,CubicPiece.primitive,tailScore,tailPrimitive,tailCoord,
    tailOne,tailTwo,StaticHigh.contact,StaticHigh.contactValue,StaticHigh.contactScore]
  all_goals (try ring)
  all_goals simp

theorem terminal_score : score 1=-1 := by
  have hb : (StaticHigh.contact:ℝ)≤1 := by norm_num [StaticHigh.contact]
  rw [(tail_values ⟨hb,le_rfl⟩).1]
  norm_num [tailScore,tailCoord,tailOne,tailTwo,StaticHigh.contact,StaticHigh.contactValue,
    StaticHigh.contactScore]

theorem terminal_primitive : primitive 1=0 := by
  have hb : (StaticHigh.contact:ℝ)≤1 := by norm_num [StaticHigh.contact]
  rw [(tail_values ⟨hb,le_rfl⟩).2]
  norm_num [tailPrimitive,tailCoord,tailOne,tailTwo,StaticHigh.contact,StaticHigh.contactValue,
    StaticHigh.contactScore]

theorem score_fall {r s : ℝ} (hr : (StaticLow.lam:ℝ)≤r) (hrs : r≤s) (hs : s≤1) :
    score s-score r≤-(s-r) := by
  have hh := quadraticConcaveChainCheck_increment concavity_checked 0 (r:=r) (s:=s)
    hr hrs (by simpa only [Rat.cast_one] using hs)
  convert! hh using 1 <;> norm_num [score,piece0]

end OptimalG.Certificates.StaticHighData
