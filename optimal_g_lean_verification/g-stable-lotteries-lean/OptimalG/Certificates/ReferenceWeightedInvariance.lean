import OptimalG.Certificates.FrozenPrefix
import OptimalG.Certificates.ReferenceHessianFrame

/-! Appending the four actual adjoint weights leaves both denominator
regularity and the full first derivative of the reference source unchanged. -/
namespace OptimalG.Certificates.Transport.ReferenceScalarCell

 theorem weightedInput_prefix (c : ReferenceScalarCell) (t : ℝ) (w : Fin 4→ℝ)
    (i : Fin 16) (hi : i.val<12) : c.weightedInput t w i=c.frozenInput t i := by
  fin_cases i <;> first | rfl | norm_num at hi

 theorem weightedInput_sourceRegular (c : ReferenceScalarCell) (t : ℝ) (w : Fin 4→ℝ)
    (late : Bool) (i : Fin 4) :
    c.params.sourceRegular late i (c.weightedInput t w)↔
      c.params.sourceRegular late i (c.frozenInput t) :=
  c.params.sourceRegular_prefix late i (c.weightedInput_prefix t w)

 theorem weightedInput_weightedFirst (c : ReferenceScalarCell) (t : ℝ)
    (w weights : Fin 4→ℝ) (late : Bool) (v : Fin 16→ℝ) :
    c.params.weightedFirst late weights (c.weightedInput t w) v=
      c.params.weightedFirst late weights (c.frozenInput t) v :=
  c.params.weightedFirst_prefix late weights (c.weightedInput_prefix t w) v

end OptimalG.Certificates.Transport.ReferenceScalarCell
