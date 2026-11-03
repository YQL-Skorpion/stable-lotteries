import OptimalG.VariationalTransportIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! Integration by parts for the rank displacement is obtained directly by
Fubini for its cumulative derivative measures. This preserves endpoint atoms
and avoids assuming absolute continuity of the matched rank. -/
namespace OptimalG.Variational
open Set MeasureTheory Function

noncomputable def cumulativeKernel (f : ℝ → ℝ) (r t : ℝ) : ℝ := if t ≤ r then f r else 0

 theorem cumulativeKernel_integrable {mu nu : Measure ℝ} [SFinite mu] [IsFiniteMeasure nu]
    {f : ℝ → ℝ} (hf : Integrable f mu) :
    Integrable (uncurry (cumulativeKernel f)) (mu.prod nu) := by
  have htri : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    isClosed_le continuous_snd continuous_fst |>.measurableSet
  exact (hf.comp_fst nu).indicator htri

 theorem cumulativeKernel_left (nu : Measure ℝ) (f : ℝ → ℝ) (r : ℝ) :
    (∫ t, cumulativeKernel f r t ∂nu) = f r*nu.real (Iic r) := by
  change (∫ t, (Iic r).indicator (fun _ => f r) t ∂nu) = _
  rw [integral_indicator measurableSet_Iic,integral_const]
  simp only [measureReal_def,Measure.restrict_apply_univ,smul_eq_mul,mul_comm]

 theorem cumulativeKernel_right (mu : Measure ℝ) (f : ℝ → ℝ) (t : ℝ) :
    (∫ r, cumulativeKernel f r t ∂mu) = ∫ r in Ici t, f r ∂mu := by
  change (∫ r, (Ici t).indicator f r ∂mu) = _
  exact integral_indicator measurableSet_Ici

 theorem cumulative_weight_integrable {mu nu : Measure ℝ} [SFinite mu] [IsFiniteMeasure nu]
    {f : ℝ → ℝ} (hf : Integrable f mu) : Integrable (fun r => f r*nu.real (Iic r)) mu := by
  have hi := (cumulativeKernel_integrable (nu:=nu) hf).integral_prod_left
  simpa only [Function.uncurry_def,cumulativeKernel_left] using hi

 theorem cumulative_potential_integrable {mu nu : Measure ℝ} [SFinite mu] [IsFiniteMeasure nu]
    {f : ℝ → ℝ} (hf : Integrable f mu) :
    Integrable (fun t => ∫ r in Ici t, f r ∂mu) nu := by
  have hi := (cumulativeKernel_integrable (nu:=nu) hf).integral_prod_right
  simpa only [Function.uncurry_def,cumulativeKernel_right] using hi

 theorem cumulative_measure_fubini {mu nu : Measure ℝ} [SFinite mu] [IsFiniteMeasure nu]
    {f : ℝ → ℝ} (hf : Integrable f mu) :
    (∫ r, f r*nu.real (Iic r) ∂mu) = ∫ t, (∫ r in Ici t, f r ∂mu) ∂nu := by
  have h := integral_integral_swap (cumulativeKernel_integrable (nu:=nu) hf)
  simpa only [cumulativeKernel_left,cumulativeKernel_right] using h

/-- The exact first-order displacement identity is valid for arbitrary
finite singular mass, including atoms at the ends of the interval. -/
theorem cumulative_displacement_fubini {mu nu : Measure ℝ}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] {f : ℝ → ℝ} (hf : Integrable f mu) :
    (∫ r, f r*(nu.real (Iic r)-mu.real (Iic r)) ∂mu) =
      (∫ t, (∫ r in Ici t, f r ∂mu) ∂nu)-(∫ t, (∫ r in Ici t, f r ∂mu) ∂mu) := by
  have he : (fun r => f r*(nu.real (Iic r)-mu.real (Iic r))) =
      (fun r => f r*nu.real (Iic r)-f r*mu.real (Iic r)) := by
    funext r
    ring
  rw [he,integral_sub (cumulative_weight_integrable hf) (cumulative_weight_integrable hf),
    cumulative_measure_fubini hf,cumulative_measure_fubini hf]

end OptimalG.Variational
