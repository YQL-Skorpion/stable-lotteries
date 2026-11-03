import OptimalG.RationalImplicit
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-!
# Arbitrarily small regular mixtures

The Jacobian of a mixture of two fixed profiles is affine in its mixing weight.
If the auxiliary endpoint is invertible, its determinant polynomial is nonzero,
so a regular mixture exists at an arbitrarily small positive weight.
-/

namespace OptimalG
open Set
open scoped Polynomial

/-- A polynomial nonzero somewhere cannot vanish throughout a nonempty open
interval, even when that interval is arbitrarily close to zero. -/
theorem polynomial_nonzero_arbitrarily_small (P : ℝ[X]) (x : ℝ)
    (hP : P.eval x ≠ 0) (eps : ℝ) (heps : 0 < eps) :
    ∃ t ∈ Ioo (0 : ℝ) eps, P.eval t ≠ 0 := by
  have hp : P ≠ 0 := by intro h; simp [h] at hP
  have hroots := Polynomial.finite_setOf_isRoot hp
  obtain ⟨t, ht, hnot⟩ := ((Set.Ioo_infinite heps).sdiff hroots).nonempty
  exact ⟨t, ht, hnot⟩

noncomputable def mixtureDeterminant {C : Type*} [Fintype C] [DecidableEq C]
    (A B : Matrix C C ℝ) : ℝ[X] :=
  Matrix.det (fun i j => Polynomial.C (A i j) + Polynomial.X * Polynomial.C (B i j - A i j))

theorem mixtureDeterminant_eval {C : Type*} [Fintype C] [DecidableEq C]
    (A B : Matrix C C ℝ) (t : ℝ) :
    (mixtureDeterminant A B).eval t = Matrix.det (fun i j => (1 - t) * A i j + t * B i j) := by
  unfold mixtureDeterminant
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp
  ring

/-- The algebraic nonsingularity step of Appendix A.4. -/
theorem matrix_regular_mixture_arbitrarily_small {C : Type*} [Fintype C] [DecidableEq C]
    (A B : Matrix C C ℝ) (hB : B.det ≠ 0) (eps : ℝ) (heps : 0 < eps) :
    ∃ t ∈ Ioo (0 : ℝ) eps, Matrix.det (fun i j => (1 - t) * A i j + t * B i j) ≠ 0 := by
  have hp : (mixtureDeterminant A B).eval 1 ≠ 0 := by
    simpa only [mixtureDeterminant_eval, sub_self, zero_mul, one_mul, zero_add] using hB
  obtain ⟨t, ht, hdet⟩ := polynomial_nonzero_arbitrarily_small (mixtureDeterminant A B) 1 hp eps heps
  exact ⟨t, ht, by simpa only [mixtureDeterminant_eval] using hdet⟩

/-- The determinant argument for genuine finite-dimensional continuous linear
operators, ready to apply to a mixture of actual profile Jacobians. -/
theorem operator_regular_mixture_arbitrarily_small
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A B : E →L[ℝ] E) (hB : B.IsInvertible) (eps : ℝ) (heps : 0 < eps) :
    ∃ t ∈ Ioo (0 : ℝ) eps, ((1 - t) • A + t • B).IsInvertible := by
  let basis := Module.finBasis ℝ E
  have hdetB : (LinearMap.toMatrix basis basis B.toLinearMap).det ≠ 0 := by
    obtain ⟨eB, heB⟩ := hB
    rw [← heB]
    exact (eB.toLinearEquiv.isUnit_det basis basis).ne_zero
  obtain ⟨t, ht, hdet⟩ := matrix_regular_mixture_arbitrarily_small
    (LinearMap.toMatrix basis basis A.toLinearMap) (LinearMap.toMatrix basis basis B.toLinearMap)
    hdetB eps heps
  let M := (1 - t) • A + t • B
  have hmatrix : LinearMap.toMatrix basis basis M.toLinearMap =
      fun i j => (1 - t) * LinearMap.toMatrix basis basis A.toLinearMap i j +
        t * LinearMap.toMatrix basis basis B.toLinearMap i j := by
    ext i j
    simp [M, LinearMap.toMatrix_apply]
  have hunit : IsUnit (LinearMap.toMatrix basis basis M.toLinearMap).det := by
    rw [hmatrix]
    exact isUnit_iff_ne_zero.mpr hdet
  refine ⟨t, ht, (LinearEquiv.ofIsUnitDet hunit).toContinuousLinearEquiv, ?_⟩
  ext x
  rfl

/-- Regular operator mixtures can be chosen inside any prescribed neighborhood
of the unperturbed profile. -/
theorem operator_regular_mixture_mem_nhds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A B : E →L[ℝ] E) (hB : B.IsInvertible) (U : Set ℝ)
    (hU : U ∈ nhds 0) : ∃ t : ℝ, 0 < t ∧ t ∈ U ∧ ((1 - t) • A + t • B).IsInvertible := by
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨t, ht, hreg⟩ := operator_regular_mixture_arbitrarily_small A B hB eps heps
  refine ⟨t, ht.1, hball ?_, hreg⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1] using ht.2

end OptimalG
