import OptimalG.VariationalContinuation
import Mathlib.Topology.Order.Compact

/-! Actual terminal contact follows from compactness and the absence of a strict margin. -/
namespace OptimalG.Variational
open Set

def terminalDomain : Set (ℝ × ℝ) := Icc zTest zEnd ×ˢ Icc qLo qHi

theorem terminalDomain_compact : IsCompact terminalDomain :=
  isCompact_Icc.prod isCompact_Icc

theorem terminalDomain_nonempty : terminalDomain.Nonempty := by
  refine ⟨(zTest, qLo), ?_⟩
  norm_num [terminalDomain, zTest, zEnd, qLo, qHi]

theorem terminalBound_continuous {lam S : ℝ} (hl : lambdaLo ≤ lam) :
    ContinuousOn (fun v : ℝ × ℝ => terminalBound lam S v.1 v.2) terminalDomain := by
  apply ContinuousOn.div
  · unfold quadratic cap
    apply ContinuousOn.mul continuous_fst.continuousOn
    apply ContinuousOn.sub
    · fun_prop
    · apply ContinuousOn.sub
      · fun_prop
      · apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro v hv
        have hh := hv.2.2
        dsimp [qHi] at hh
        linarith
  · fun_prop
  · intro v hv
    have hh := hv.2.2
    dsimp [lambdaLo] at hl
    dsimp [qHi] at hh
    linarith

theorem terminalResidual_continuous {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) :
    ContinuousOn (fun v : ℝ × ℝ => terminalBound lam d.S v.1 v.2 -
      continuation lam d v.1) terminalDomain := by
  apply (terminalBound_continuous hd.1.1).sub
  apply (continuation_continuous hd.isContinuation).comp continuous_fst.continuousOn
  intro v hv
  refine ⟨?_, hv.1.2⟩
  have hh := hv.1.1
  dsimp [zStart, zTest] at *
  linarith

/-- A feasible canonical continuation with no uniform strict terminal margin
touches one of the actual terminal barriers. -/
theorem terminal_contact_of_no_strict_margin {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d)
    (ht : PassesTerminalTests lam d (continuation lam d))
    (hno : ¬ ∃ delta > 0, ∀ z ∈ Icc zTest zEnd, ∀ q ∈ Icc qLo qHi,
      terminalBound lam d.S z q + delta ≤ continuation lam d z) :
    ∃ z ∈ Icc zTest zEnd, ∃ q ∈ Icc qLo qHi,
      terminalBound lam d.S z q = continuation lam d z := by
  obtain ⟨v, hv, hmax⟩ := terminalDomain_compact.exists_isMaxOn
    terminalDomain_nonempty (terminalResidual_continuous hd)
  refine ⟨v.1, hv.1, v.2, hv.2, ?_⟩
  have hle := ht v.1 hv.1 v.2 hv.2
  apply le_antisymm hle
  by_contra hgt
  have hstrict : terminalBound lam d.S v.1 v.2 < continuation lam d v.1 := lt_of_not_ge hgt
  apply hno
  refine ⟨continuation lam d v.1 - terminalBound lam d.S v.1 v.2, sub_pos.mpr hstrict, ?_⟩
  intro z hz q hq
  have hh := hmax (show (z, q) ∈ terminalDomain from ⟨hz, hq⟩)
  dsimp at hh
  linarith

end OptimalG.Variational
