import OptimalG.SymmetricTangent
import OptimalG.ScoreRelabel
import OptimalG.LowerElection

/-! # The fully symmetric baseline profile and its scalar tangent derivative -/

namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

noncomputable def fullSymmetricScore {m : ℕ} (g : ℝ → ℝ) (D : Fin m → ℝ) : Fin m → ℝ :=
  fun a => (∑ order : Equiv.Perm (Fin m), scoreExtension g order a D) /
    Fintype.card (Equiv.Perm (Fin m))

noncomputable def fullSymmetricDerivative {m : ℕ} (g : ℝ → ℝ) (u : ℝ) :
    (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi (fun a => (1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ)) •
    ∑ order : Equiv.Perm (Fin m), scoreDerivative g order a (fun _ => u))

theorem fullSymmetricDerivative_apply {m : ℕ} (g : ℝ → ℝ) (u : ℝ)
    (h : Fin m → ℝ) (a : Fin m) :
    fullSymmetricDerivative g u h a =
      (∑ order : Equiv.Perm (Fin m), scoreDerivative g order a (fun _ => u) h) /
        Fintype.card (Equiv.Perm (Fin m)) := by
  simp [fullSymmetricDerivative, div_eq_mul_inv, mul_comm]

theorem fullSymmetricScore_hasStrictFDerivAt {m : ℕ} (g : ℝ → ℝ)
    (hg : Continuous g) (u : ℝ) (hu : u ≠ 0) :
    HasStrictFDerivAt (fullSymmetricScore g) (fullSymmetricDerivative g u) (fun _ => u : Fin m → ℝ) := by
  apply hasStrictFDerivAt_pi.mpr
  intro a
  have hs := HasStrictFDerivAt.fun_sum (u := Finset.univ)
    (fun (order : Equiv.Perm (Fin m)) _ => scoreExtension_hasStrictFDerivAt g hg order a (fun _ => u) hu)
  convert! hs.const_smul (1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ)) using 1
  funext D
  simp [fullSymmetricScore, div_eq_mul_inv, mul_comm]

/-- The derivative commutes with every relabeling, proved by reindexing the
finite sum over all rankings. -/
theorem fullSymmetricDerivative_equivariant {m : ℕ} (g : ℝ → ℝ) (u : ℝ) (hu : u ≠ 0)
    (sigma : Equiv.Perm (Fin m)) (h : Fin m → ℝ) :
    fullSymmetricDerivative g u (fun a => h (sigma a)) =
      fun a => fullSymmetricDerivative g u h (sigma a) := by
  funext a
  rw [fullSymmetricDerivative_apply, fullSymmetricDerivative_apply]
  congr 1
  have hpoint (order : Equiv.Perm (Fin m)) :
      scoreDerivative g order a (fun _ => u) (fun x => h (sigma x)) =
      scoreDerivative g (sigma * order) (sigma a) (fun _ => u) h := by
    exact (scoreDerivative_relabel g order sigma a (fun _ => u) h hu).symm
  simp_rw [hpoint]
  exact Equiv.sum_comp (Equiv.mulLeft sigma)
    (fun order => scoreDerivative g order (sigma a) (fun _ => u) h)

/-- The scalar-baseline claim in Appendix A.4 for the actual score derivative. -/
theorem fullSymmetricDerivative_scalar_on_tangent {m : ℕ} [Nontrivial (Fin m)]
    (g : ℝ → ℝ) (u : ℝ) (hu : u ≠ 0) :
    ∃ scalar : ℝ, ∀ h : Fin m → ℝ, (∑ a, h a) = 0 →
      fullSymmetricDerivative g u h = scalar • h := by
  exact scalar_on_tangent_of_permutation_equivariant
    (fullSymmetricDerivative g u).toLinearMap (fullSymmetricDerivative_equivariant g u hu)

/-- The baseline is stationary at the uniform probability lottery. -/
theorem fullSymmetricScore_stationary {m : ℕ} [NeZero m] (g : ℝ → ℝ)
    (hg : Continuous g) (a : Fin m) :
    fullSymmetricScore g (fun _ : Fin m => 1 / (m : ℝ)) a = ∫ r in (0 : ℝ)..1, g r := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hmass : (1 / (m : ℝ)) ≠ 0 := one_div_ne_zero hm
  have hbase := full_symmetry_stationary g (fun _ : Fin m => 1 / (m : ℝ)) (Equiv.refl (Fin m))
    hg.continuousOn (fun _ => by positivity) (by simp [hm]) (fun _ _ => rfl) a
  unfold fullSymmetricScore
  simp_rw [scoreExtension_eq_orderedActivation g hg _ a (fun _ : Fin m => 1 / (m : ℝ)) hmass]
  exact hbase

end OptimalG
