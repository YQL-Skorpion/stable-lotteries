import OptimalG.Certificates.FiniteStepIntegral
import OptimalG.Certificates.TransportHessianCell

/-! Integral semantics for the finite Hessian bounds along the reference
flow. Rational summary sums become genuine integrals of the step fields. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

def hessianCellCoverCheck (start finish : ℚ) (cells : List HessianCell) : Bool :=
  stepCoverCheck HessianCell.zLo HessianCell.zHi start finish cells

noncomputable def hessianStepField (value : HessianCell → ℚ)
    (cells : List HessianCell) : ℝ → ℝ :=
  finiteStep HessianCell.zHi (fun c => (value c : ℝ)) cells

theorem hessianStepField_nonneg (value : HessianCell → ℚ)
    {cells : List HessianCell} (hv : ∀ c ∈ cells, 0 ≤ value c) (z : ℝ) :
    0 ≤ hessianStepField value cells z := by
  induction cells with
  | nil => exact le_rfl
  | cons c cs ih =>
    change 0 ≤ if z ≤ (c.zHi : ℝ) then (value c : ℝ) else
      hessianStepField value cs z
    split_ifs
    · exact_mod_cast hv c (by simp)
    · exact ih (fun d hd => hv d (by simp [hd]))

theorem hessianCellCoverCheck_append {start middle finish : ℚ}
    {xs ys : List HessianCell}
    (hx : hessianCellCoverCheck start middle xs = true)
    (hy : hessianCellCoverCheck middle finish ys = true) :
    hessianCellCoverCheck start finish (xs ++ ys) = true :=
  stepCoverCheck_append hx hy

theorem hessianCellCoverCheck_cover {start finish : ℚ} {cells : List HessianCell}
    (hc : hessianCellCoverCheck start finish cells = true) {z : ℝ}
    (hz : z ∈ Ioc (start : ℝ) (finish : ℝ)) :
    ∃ c ∈ cells, z ∈ Ioc (c.zLo : ℝ) (c.zHi : ℝ) :=
  stepCoverCheck_cover hc hz

theorem hessianStepField_eq_of_mem {start finish : ℚ} {cells : List HessianCell}
    (hc : hessianCellCoverCheck start finish cells = true)
    (value : HessianCell → ℚ) {c : HessianCell} (hm : c ∈ cells)
    {z : ℝ} (hz : z ∈ Ioc (c.zLo : ℝ) (c.zHi : ℝ)) :
    hessianStepField value cells z = (value c : ℝ) :=
  finiteStep_eq_of_mem hc hm hz

theorem hessianStepField_intervalIntegrable {start finish : ℚ} {cells : List HessianCell}
    (hc : hessianCellCoverCheck start finish cells = true) (value : HessianCell → ℚ) :
    IntervalIntegrable (hessianStepField value cells) volume (start : ℝ) (finish : ℝ) :=
  (finiteStep_integral (fun c => (value c : ℝ)) hc).1

theorem hessianStepField_integral {start finish : ℚ} {cells : List HessianCell}
    (hc : hessianCellCoverCheck start finish cells = true) (value : HessianCell → ℚ) :
    (∫ z in (start : ℝ)..(finish : ℝ), hessianStepField value cells z) =
      ((cells.map fun c => (c.zHi - c.zLo) * value c).sum : ℚ) :=
  finiteStep_integral_rat value hc

theorem scalarLower_integral {start finish : ℚ} {cells : List HessianCell}
    (hc : hessianCellCoverCheck start finish cells = true) :
    (∫ z in (start : ℝ)..(finish : ℝ), hessianStepField HessianCell.scalarLower cells z) =
      ((cells.map fun c => (c.zHi - c.zLo) * c.scalarLower).sum : ℚ) :=
  hessianStepField_integral hc HessianCell.scalarLower

theorem rankPenalty_integral {start finish : ℚ} {cells : List HessianCell}
    (hc : hessianCellCoverCheck start finish cells = true) :
    (∫ z in (start : ℝ)..(finish : ℝ), hessianStepField HessianCell.rankPenalty cells z) =
      ((cells.map fun c => (c.zHi - c.zLo) * c.rankPenalty).sum : ℚ) :=
  hessianStepField_integral hc HessianCell.rankPenalty

end OptimalG.Certificates.Transport
