import OptimalG.ParameterTransferTerminal
import OptimalG.PhaseContinuation

/-! A genuine high continuation and all terminal inequalities for the upward
parameter competitor. No trajectory is supplied as an unproved input. -/
namespace OptimalG.Variational.ParameterTransfer
open Set

theorem exists_shifted_continuation {lam delta : ℝ} {d : LowRankData} {Y : ℝ → ℝ}
    (h : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hd : 0 ≤ delta) (hY : IsContinuation lam d Y) (htest : PassesTerminalTests lam d Y) :
    ∃ Z : ℝ → ℝ,
      Z zStart=quadratic (lam+delta) zStart-scalar d.S delta ∧
      (∀ z ∈ Icc zStart zEnd,HasDerivWithinAt Z
        (rawVectorField (lam+delta) (shiftedPrimitive lam d delta) d.phi z (Z z)) (Icc zStart zEnd) z) ∧
      (∀ z ∈ Icc zStart zEnd,Y z+0.26412*delta ≤ Z z ∧
        quadratic (lam+delta) z-quadratic (lam+delta) 1 ≤ Z z ∧
        Z z ≤ quadratic (lam+delta) z-scalar d.S delta) ∧
      ∀ z ∈ Icc zTest zEnd,∀ q ∈ Icc qLo qHi,
        z*(shiftedPrimitive lam d delta (1-z+q)-shiftedPrimitive lam d delta q)/(lam+delta-q)+
          0.07812*delta ≤ Z z := by
  have hYlo (z : ℝ) (hz : z ∈ Icc zStart zEnd) : quadratic lam z-quadratic lam 1 ≤ Y z := by
    have hh := h.continuation_above_root_budget hY htest hz
    linarith
  have hYhi := h.continuation_le_quadratic hY
  obtain ⟨K,hK,htime⟩ := shifted_regular h hLnew hd
  let Sbase := d.S+delta*zStart
  have hT : 0 ≤ scalar d.S delta := by
    have hs : 0 ≤ d.S := by linarith [h.slack_lower]
    unfold scalar
    positivity
  have hST : scalar d.S delta=Sbase-0.5738*delta := by
    dsimp [scalar,Sbase,zStart]
    ring
  have hY0 : Y zStart=linePrimitive (lam+delta) zStart-Sbase := by
    rw [hY.1]
    dsimp [Sbase,linePrimitive,quadratic]
    ring
  have hYbounds (z : ℝ) (hz : z ∈ Icc zStart zEnd) :
      linePrimitive (lam+delta) z-linePrimitive (lam+delta) 1 ≤ Y z ∧
        Y z ≤ linePrimitive (lam+delta) z-Sbase := by
    have hzl : zStart ≤ z := hz.1
    have hzu : z ≤ 1 := hz.2.trans (by norm_num [zEnd])
    have hlowDelta := mul_nonpos_of_nonneg_of_nonpos hd (sub_nonpos.mpr hzu)
    have hhighDelta := mul_nonneg hd (sub_nonneg.mpr hzl)
    have hl := hYlo z hz
    have hh := hYhi z hz
    dsimp [Sbase,linePrimitive,quadratic] at *
    constructor <;> nlinarith only [hl,hh,hlowDelta,hhighDelta]
  have hfield (z : ℝ) (hz : z ∈ Icc zStart zEnd) :
      vectorField lam d z (Y z)-(6.19*(0.395*delta)+4.53*phaseError (0.395*delta) z) ≤
        rawVectorField (lam+delta) (shiftedPrimitive lam d delta) d.phi z
          (Y z+0.5738*delta-phaseError (0.395*delta) z) :=
    field_comparison h hLnew hd hz (hYlo z hz) (hYhi z hz) (phaseError_bounds (by positivity) hz)
  obtain ⟨Z,hZ0,hZD,hZB⟩ := exists_phase_continuation (lam := lam+delta)
    (S := Sbase) (T := scalar d.S delta) (gain := 0.5738*delta) (mu := 0.395*delta)
    hLnew (vectorField lam d) (rawVectorField (lam+delta) (shiftedPrimitive lam d delta) d.phi) K Y
    (by positivity) (by linarith) hT hST hK htime hY0 hY.2 hYbounds hfield
    (fun z u => min_le_left _ _)
  have hflow (z : ℝ) (hz : z ∈ Icc zStart zEnd) : Y z+0.26412*delta ≤ Z z := by
    have hh := (hZB z hz).1
    linarith
  refine ⟨Z,hZ0,hZD,fun z hz => ⟨hflow z hz,(hZB z hz).2⟩,?_⟩
  exact transferred_terminal_tests h hd htest hYlo hflow

end OptimalG.Variational.ParameterTransfer
