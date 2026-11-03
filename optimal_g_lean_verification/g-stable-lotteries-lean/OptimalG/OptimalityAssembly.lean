import OptimalG.Election

/-! Order-theoretic assembly of exact optimality from universal upper bounds and
finite epsilon-witnesses. This does not supply those substantive hypotheses. -/

namespace OptimalG

open scoped ENNReal

theorem witnessAbove_le_maximumDistortion (g : ℝ → ℝ) (K : ℝ)
    (hw : WitnessAbove g K) : ENNReal.ofReal K ≤ maximumDistortion g := by
  rcases hw with ⟨E, D, hs, d, hc, a, hpos, hstrict⟩
  apply le_iSup_of_le E
  apply le_iSup_of_le D
  apply le_iSup_of_le hs
  apply le_iSup_of_le d
  apply le_iSup_of_le hc
  apply le_iSup_of_le a
  simp only [costRatio, if_neg (ne_of_gt hpos)]
  exact ENNReal.ofReal_le_ofReal ((lt_div_iff₀ hpos).mpr hstrict).le

/-- Arbitrarily close finite strict lower witnesses imply a sharp supremum lower bound. -/
theorem maximumDistortion_lower_of_witnesses (g : ℝ → ℝ) (K : ℝ)
    (hw : ∀ eps : ℝ, 0 < eps → WitnessAbove g (K - eps)) :
    ENNReal.ofReal K ≤ maximumDistortion g := by
  by_contra h
  have hlt : maximumDistortion g < ENNReal.ofReal K := lt_of_not_ge h
  have hfinite : maximumDistortion g ≠ ⊤ := ne_top_of_lt hlt
  have hreal : (maximumDistortion g).toReal < K := ENNReal.toReal_lt_of_lt_ofReal hlt
  let eps := (K - (maximumDistortion g).toReal) / 2
  have heps : 0 < eps := by dsimp [eps]; linarith
  have hwitness := witnessAbove_le_maximumDistortion g (K - eps) (hw eps heps)
  have hrealbound := (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hwitness
  dsimp [eps] at hrealbound
  linarith

/-- Final logical assembly, with the actual finite-election `maximumDistortion`.
The hard work is constructing `gstar` and proving `hupper` and `hlower`. -/
theorem assemble_optimality (gstar : ℝ → ℝ) (K : ℝ) (hK : 1 ≤ K)
    (hgstar : AdmissibleActivation gstar) (hupper : UniversalBound gstar K)
    (hlower : ∀ g : ℝ → ℝ, AdmissibleActivation g →
      ∀ eps : ℝ, 0 < eps → WitnessAbove g (K - eps)) :
    maximumDistortion gstar = ENNReal.ofReal K ∧
      ∀ g : ℝ → ℝ, AdmissibleActivation g → maximumDistortion gstar ≤ maximumDistortion g := by
  have heq : maximumDistortion gstar = ENNReal.ofReal K := le_antisymm
    ((maximumDistortion_le_iff gstar K hK).mpr hupper)
    (maximumDistortion_lower_of_witnesses gstar K (hlower gstar hgstar))
  refine ⟨heq, ?_⟩
  intro g hg
  rw [heq]
  exact maximumDistortion_lower_of_witnesses g K (hlower g hg)

end OptimalG
