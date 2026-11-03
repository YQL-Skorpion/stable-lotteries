import OptimalG.OptimalityAssembly

/-! A finite bracket for the infimum over every admissible activation. -/
namespace OptimalG
open scoped ENNReal

noncomputable def optimalDistortion : ℝ≥0∞ :=
  ⨅ (g : ℝ→ℝ) (_ : AdmissibleActivation g),maximumDistortion g

theorem assemble_approximate_optimality {lower upper : ℝ}
    (hupper_one : 1≤upper) (gstar : ℝ→ℝ)
    (hgstar : AdmissibleActivation gstar) (hupper : UniversalBound gstar upper)
    (hlower : ∀ g : ℝ→ℝ,AdmissibleActivation g →
      ENNReal.ofReal lower≤maximumDistortion g) :
    ENNReal.ofReal lower≤optimalDistortion ∧
      optimalDistortion≤ENNReal.ofReal upper := by
  constructor
  · exact le_iInf fun g => le_iInf fun hg => hlower g hg
  · exact iInf_le_of_le gstar (iInf_le_of_le hgstar
      ((maximumDistortion_le_iff gstar upper hupper_one).mpr hupper))

theorem rational_bracket_width :
    (106233/50000:ℝ)-(42493/20000)=1/100000 := by norm_num

end OptimalG
