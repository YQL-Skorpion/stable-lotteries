import OptimalG.ScoreDerivative

/-! # Relabeling the actual score map and its derivative -/

namespace OptimalG

/-- Relabeling candidates pulls back the lottery weights in the rank-prefix map. -/
theorem rankPrefixLinear_relabel {m : ℕ} (order sigma : Equiv.Perm (Fin m))
    (a : Fin m) (D : Fin m → ℝ) :
    rankPrefixLinear (order.trans sigma) (sigma a) D =
      rankPrefixLinear order a (fun x => D (sigma x)) := by
  rw [rankPrefixLinear_apply, rankPrefixLinear_apply]
  simp only [Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_apply_apply]

theorem scoreExtension_relabel {m : ℕ} (g : ℝ → ℝ) (order sigma : Equiv.Perm (Fin m))
    (a : Fin m) (D : Fin m → ℝ) :
    scoreExtension g (order.trans sigma) (sigma a) D =
      scoreExtension g order a (fun x => D (sigma x)) := by
  simp only [scoreExtension, rankPrefixLinear_relabel]

/-- The derivative transforms by the same candidate relabeling as the score. -/
theorem scoreDerivative_relabel {m : ℕ} (g : ℝ → ℝ) (order sigma : Equiv.Perm (Fin m))
    (a : Fin m) (D h : Fin m → ℝ) (hDa : D (sigma a) ≠ 0) :
    scoreDerivative g (order.trans sigma) (sigma a) D h =
      scoreDerivative g order a (fun x => D (sigma x)) (fun x => h (sigma x)) := by
  rw [scoreDerivative_apply g (order.trans sigma) (sigma a) D h hDa,
    scoreDerivative_apply g order a (fun x => D (sigma x)) (fun x => h (sigma x)) hDa]
  simp only [rankPrefixLinear_relabel, scoreExtension_relabel]

theorem orderedActivation_relabel_weights {m : ℕ} (g : ℝ → ℝ)
    (order sigma : Equiv.Perm (Fin m)) (a : Fin m) (D : Fin m → ℝ) :
    orderedActivation g D (order.trans sigma) (sigma a) =
      orderedActivation g (fun x => D (sigma x)) order a := by
  simp only [orderedActivation, rankActivation, Equiv.symm_trans_apply,
    Equiv.symm_apply_apply, Equiv.trans_apply]

end OptimalG
