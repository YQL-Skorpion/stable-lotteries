import OptimalG.ScoreDerivative

/-!
# Local cyclic-triple derivative calculation

These lemmas calculate the derivative of the six actual candidate order scores
appearing in Appendix A.4. Their prefix-mass premises describe a consecutive
triple in a ranking; the calculation does not assume the stated Jacobian.
-/

namespace OptimalG
open scoped BigOperators

noncomputable def localScoreVariation (g G : ℝ → ℝ) (s u H own : ℝ) : ℝ :=
  (g (s + u) * (H + own) - g s * H - ((G (s + u) - G s) / u) * own) / u

/-- The own-mass and primitive terms cancel because each candidate has the same
position marginal in the cyclic and reversed profiles. -/
theorem cyclic_local_variation (g G : ℝ → ℝ) (s u H own left right : ℝ)
    (hu : u ≠ 0) :
    (localScoreVariation g G s u H own +
      localScoreVariation g G (s + 2 * u) u (H + left + right) own +
      localScoreVariation g G (s + u) u (H + right) own -
      localScoreVariation g G (s + 2 * u) u (H + right + left) own -
      localScoreVariation g G s u H own -
      localScoreVariation g G (s + u) u (H + left) own) / 3 =
        ((g (s + 2 * u) - g (s + u)) / (3 * u)) * (right - left) := by
  have hs : s + u + u = s + 2 * u := by ring
  unfold localScoreVariation
  rw [hs]
  field_simp
  ring

/-- The signed cyclic derivative for one of the three candidates, from actual
rank-prefix masses and actual rank-prefix variations. -/
theorem cyclic_actual_score_derivative {m : ℕ}
    (g : ℝ → ℝ) (orders : Fin 6 → Equiv.Perm (Fin m))
    (a : Fin m) (D h : Fin m → ℝ) (s u H left right : ℝ)
    (hu : u ≠ 0) (hmass : D a = u)
    (hprefix : ∀ i, rankPrefixLinear (orders i) a D =
      ![s, s + 2 * u, s + u, s + 2 * u, s, s + u] i)
    (hvariation : ∀ i, rankPrefixLinear (orders i) a h =
      ![H, H + left + right, H + right, H + right + left, H, H + left] i) :
    (scoreDerivative g (orders 0) a D h + scoreDerivative g (orders 1) a D h +
      scoreDerivative g (orders 2) a D h - scoreDerivative g (orders 3) a D h -
      scoreDerivative g (orders 4) a D h - scoreDerivative g (orders 5) a D h) / 3 =
        ((g (s + 2 * u) - g (s + u)) / (3 * u)) * (right - left) := by
  have hDa : D a ≠ 0 := hmass ▸ hu
  have hlocal (i : Fin 6) : scoreDerivative g (orders i) a D h =
      localScoreVariation g (activationPrimitive g)
        (rankPrefixLinear (orders i) a D) u (rankPrefixLinear (orders i) a h) (h a) := by
    rw [scoreDerivative_apply g (orders i) a D h hDa]
    simp only [scoreExtension, hmass, localScoreVariation]
  simp only [hlocal, hprefix, hvariation, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue]
  exact cyclic_local_variation g (activationPrimitive g) s u H (h a) left right hu

/-- Any unaffected candidate contributes zero when its six prefix data agree. -/
theorem cyclic_unaffected_score_derivative {m : ℕ}
    (g : ℝ → ℝ) (orders : Fin 6 → Equiv.Perm (Fin m))
    (a : Fin m) (D h : Fin m → ℝ) (hDa : D a ≠ 0)
    (hprefix : ∀ i, rankPrefixLinear (orders i) a D = rankPrefixLinear (orders 0) a D)
    (hvariation : ∀ i, rankPrefixLinear (orders i) a h = rankPrefixLinear (orders 0) a h) :
    (scoreDerivative g (orders 0) a D h + scoreDerivative g (orders 1) a D h +
      scoreDerivative g (orders 2) a D h - scoreDerivative g (orders 3) a D h -
      scoreDerivative g (orders 4) a D h - scoreDerivative g (orders 5) a D h) / 3 = 0 := by
  have hsame (i : Fin 6) : scoreDerivative g (orders i) a D h = scoreDerivative g (orders 0) a D h := by
    rw [scoreDerivative_apply g (orders i) a D h hDa,
      scoreDerivative_apply g (orders 0) a D h hDa]
    simp only [scoreExtension, hprefix, hvariation]
  simp only [hsame]
  ring

end OptimalG
