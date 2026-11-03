import OptimalG.AuxiliarySkew
import Mathlib.Logic.Equiv.Fintype

/-! # Permutation-invariant linear maps on the lottery tangent space -/

namespace OptimalG
open scoped BigOperators

noncomputable def coordinateUnit {C : Type*} [DecidableEq C] (b : C) : C → ℝ :=
  fun a => if a = b then 1 else 0

theorem coordinateUnit_relabel {C : Type*} [DecidableEq C]
    (sigma : Equiv.Perm C) (b : C) :
    (fun a => coordinateUnit (sigma b) (sigma a)) = coordinateUnit b := by
  funext a
  simp only [coordinateUnit, sigma.injective.eq_iff]

/-- A linear map commuting with all candidate permutations acts as a scalar on
the zero-sum space; no representation-theoretic assertion is assumed. -/
theorem scalar_on_tangent_of_permutation_equivariant
    {C : Type*} [Fintype C] [DecidableEq C] [Nontrivial C]
    (L : (C → ℝ) →ₗ[ℝ] (C → ℝ))
    (hcomm : ∀ (sigma : Equiv.Perm C) (h : C → ℝ),
      L (fun a => h (sigma a)) = fun a => L h (sigma a)) :
    ∃ scalar : ℝ, ∀ h : C → ℝ, (∑ a, h a) = 0 → L h = scalar • h := by
  obtain ⟨a0, b0, hab0⟩ := exists_pair_ne C
  let K := fun a b => L (coordinateUnit b) a
  have hK (sigma : Equiv.Perm C) (a b : C) : K (sigma a) (sigma b) = K a b := by
    have hh := congrArg (fun f : C → ℝ => f a) (hcomm sigma (coordinateUnit (sigma b)))
    rw [coordinateUnit_relabel] at hh
    exact hh.symm
  have hdiag (a : C) : K a a = K a0 a0 := by
    have hh := hK (Equiv.swap a0 a) a0 a0
    simpa using hh
  have hoff (a b : C) (hab : a ≠ b) : K a b = K a0 b0 := by
    have hi : Function.Injective (![a0, b0] : Fin 2 → C) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have hj : Function.Injective (![a, b] : Fin 2 → C) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    obtain ⟨sigma, hsigma⟩ := Equiv.Perm.exists_extending_pair ![a0, b0] ![a, b] hi hj
    have ha : sigma a0 = a := hsigma 0
    have hb : sigma b0 = b := hsigma 1
    simpa only [ha, hb] using hK sigma a0 b0
  let diag := K a0 a0
  let off := K a0 b0
  have hentry (a b : C) : K a b = off + if b = a then diag - off else 0 := by
    by_cases hab : b = a
    · subst b
      rw [hdiag]
      simp only [if_true]
      dsimp [diag, off]
      ring
    · rw [hoff a b (Ne.symm hab)]
      simp only [if_neg hab, add_zero]
      rfl
  refine ⟨diag - off, ?_⟩
  intro h hsum
  have hexpand : h = ∑ b, h b • coordinateUnit b := by
    funext a
    simp [coordinateUnit, Finset.sum_apply, Pi.smul_apply]
  have hlinear : ∀ a, L h a = ∑ b, h b * K a b := by
    intro a
    conv_lhs => rw [hexpand]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, K]
  funext a
  rw [hlinear]
  simp_rw [hentry, mul_add, mul_ite, mul_zero]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, zero_mul, zero_add]
  simp
  ring

end OptimalG
