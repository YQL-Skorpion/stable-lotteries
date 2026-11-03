import OptimalG.Certificates.StaticCurve
import OptimalG.BinarySmallCentral

namespace OptimalG.Certificates.StaticCurve
open Set Variational

/-- Exact state barriers for the explicit curve, derived from its score ceiling
and its two normalized primitive values. -/
theorem state_sandwich {r : ℝ} (hr : r∈Icc (StaticLow.lam:ℝ) 1) :
    Variational.quadratic StaticLow.lam r-Variational.quadratic StaticLow.lam 1≤
      curvePrimitive score r ∧
    curvePrimitive score r≤Variational.quadratic StaticLow.lam r-StaticLow.slack := by
  have hL : (StaticLow.lam:ℝ)∈Icc (0:ℝ) 1 := by norm_num [StaticLow.lam]
  have hr0 : r∈Icc (0:ℝ) 1 := ⟨hL.1.trans hr.1,hr.2⟩
  have hlower := verifierCurve.primitive_relative_quadratic_antitone hr0
    (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num) hr.2
  have hupper := verifierCurve.primitive_relative_quadratic_antitone hL hr0 hr.1
  have hz : curvePrimitive score 1=0 := verifierCurve.integral_zero
  have hj : curvePrimitive score StaticLow.lam=
      Variational.quadratic StaticLow.lam StaticLow.lam-StaticLow.slack := by
    change primitive StaticLow.lam=_
    rw [high_primitive le_rfl,StaticHighData.initial_primitive]
    unfold Certificates.quadratic Variational.quadratic
    ring
  dsimp only at hlower hupper
  rw [hz] at hlower
  rw [hj] at hupper
  constructor <;> linarith only [hlower,hupper]

end OptimalG.Certificates.StaticCurve
