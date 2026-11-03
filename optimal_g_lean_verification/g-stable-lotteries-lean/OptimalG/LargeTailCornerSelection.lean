import OptimalG.LargeTailMassBounds

namespace OptimalG
open Set Certificates.LargeTailExpressions

/-- Select the two mass endpoints and two score endpoints, identifying the
coincident mass endpoints before the line ends. -/
theorem largeTail_corner_selection {lam S p : ℝ} {P : ℝ→ℝ→Prop}
    (hline0 : p≤391/500→P (massCap lam S p) (-3589/10000))
    (hline1 : p≤391/500→P (massCap lam S p) (-1757/5000))
    (hlower0 : 391/500≤p→P (massLower lam S p) (-3589/10000))
    (hlower1 : 391/500≤p→P (massLower lam S p) (-1757/5000))
    (hupper0 : 391/500≤p→P (massCap lam S p) (-3589/10000))
    (hupper1 : 391/500≤p→P (massCap lam S p) (-1757/5000)) :
    ∀ M,(M=largeTailMassFloor lam S p ∨ M=massCap lam S p)→
      ∀ H,(H= -3589/10000 ∨ H= -1757/5000)→P M H := by
  intro M hM H hH
  by_cases hpl : p≤391/500
  · simp only [largeTailMassFloor,if_pos hpl,or_self] at hM
    rw [hM]
    rcases hH with rfl | rfl
    · exact hline0 hpl
    · exact hline1 hpl
  · simp only [largeTailMassFloor,if_neg hpl] at hM
    rcases hM with rfl | rfl <;> rcases hH with rfl | rfl
    · exact hlower0 (le_of_not_ge hpl)
    · exact hlower1 (le_of_not_ge hpl)
    · exact hupper0 (le_of_not_ge hpl)
    · exact hupper1 (le_of_not_ge hpl)

end OptimalG
