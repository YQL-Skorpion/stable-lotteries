import OptimalG.AuxiliaryProfile
import OptimalG.ProfileJacobian
import OptimalG.FullSymmetryDerivative

/-!
# A strictly positive stationary profile with regular lottery derivative

This constructs the auxiliary profile of Appendix A.4 on an odd support from
actual rankings. The derivative's injectivity is checked on the actual lottery
tangent, by transporting the paired skew calculation through a candidate
labeling. No existence of a regular profile is assumed.
-/

namespace OptimalG
open MeasureTheory
open scoped BigOperators

/-- The finite auxiliary profile: all ranking weights are positive, the uniform
lottery is exactly stationary, and its actual Jacobian has no tangent kernel. -/
theorem exists_regular_auxiliary_profile {n m : ℕ} (g : ℝ → ℝ) (hg : Continuous g)
    (e : PairedSupport n ≃ Fin m) (a b c : Fin m)
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (hstrength : cyclicStrength g a (1 / (m : ℝ)) ≠ 0) :
    ∃ w : Equiv.Perm (Fin m) → ℝ,
      (∀ order, 0 < w order) ∧ (∑ order, w order) = 1 ∧
      (∀ x, expectation w (fun order => scoreExtension g order x (fun _ => 1 / (m : ℝ))) =
        ∫ r in (0 : ℝ)..1, g r) ∧
      (∀ h : Fin m → ℝ, (∑ x, h x) = 0 →
        profileLotteryJacobian g id w (fun _ => 1 / (m : ℝ)) h = 0 → h = 0) := by
  have hmpos : 0 < m := Nat.zero_lt_of_lt a.isLt
  letI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  have hab' : a ≠ b := by intro h; subst b; omega
  letI : Nontrivial (Fin m) := nontrivial_of_ne a b hab'
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hmpos
  let u : ℝ := 1 / (m : ℝ)
  have hu : u ≠ 0 := one_div_ne_zero hm
  obtain ⟨W, hWtotal, hWstationary, hWjac⟩ := exists_paired_skew_profile g e a b c hab hbc u hu
  obtain ⟨eps, heps, hpositive, htotal⟩ := exists_positive_uniform_perturbation W hWtotal
  obtain ⟨scalar, hscalar⟩ := fullSymmetricDerivative_scalar_on_tangent (m := m) g u hu
  let w : Equiv.Perm (Fin m) → ℝ := fun order =>
    1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ) + eps * W order
  have hWextension (x : Fin m) : expectation W (fun order => scoreExtension g order x (fun _ => u)) = 0 := by
    unfold expectation
    simp_rw [scoreExtension_eq_orderedActivation g hg _ x (fun _ => u) hu]
    exact hWstationary x
  have hbase (x : Fin m) : expectation (fun _ : Equiv.Perm (Fin m) =>
      1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ))
      (fun order => scoreExtension g order x (fun _ => u)) = ∫ r in (0 : ℝ)..1, g r := by
    have hh := fullSymmetricScore_stationary g hg x (m := m)
    unfold fullSymmetricScore at hh
    unfold expectation
    rw [← Finset.mul_sum]
    simpa only [u, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hh
  have hstationary : ∀ x, expectation w (fun order => scoreExtension g order x (fun _ => u)) =
      ∫ r in (0 : ℝ)..1, g r :=
    stationary_uniform_perturbation W (fun order x => scoreExtension g order x (fun _ => u))
      _ eps hbase hWextension
  refine ⟨w, hpositive, htotal, hstationary, ?_⟩
  intro h hsum hzero
  have hcoord (q : PairedSupport n) :
      profileLotteryJacobian g id w (fun _ => u) h (e q) =
        scalar * h (e q) + eps * pairedSkew n (cyclicStrength g a u) (fun q => h (e q)) q := by
    rw [profileLotteryJacobian_apply]
    change expectation (fun order => 1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ) + eps * W order)
      (fun order => scoreDerivative g order (e q) (fun _ => u) h) = _
    unfold expectation
    simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hs := congrArg (fun f : Fin m → ℝ => f (e q)) (hscalar h hsum)
    rw [fullSymmetricDerivative_apply] at hs
    have hw := hWjac h q
    unfold expectation at hw
    rw [hw]
    change 1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ) *
      (∑ order, scoreDerivative g order (e q) (fun _ => u) h) + _ = _
    simpa only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_one, one_mul] using
      congrArg (fun z => z + eps * pairedSkew n (cyclicStrength g a u) (fun q => h (e q)) q) hs
  have htransported : (fun q : PairedSupport n => h (e q)) = 0 := by
    apply pairedSkew_scalar_injective_on_tangent n (cyclicStrength g a u) scalar eps hstrength (ne_of_gt heps)
    · simpa only [Equiv.sum_comp] using hsum
    · intro q
      have hz := congrArg (fun f : Fin m → ℝ => f (e q)) hzero
      rw [hcoord] at hz
      exact hz
  funext x
  obtain ⟨q, rfl⟩ := e.surjective x
  exact congrArg (fun f : PairedSupport n → ℝ => f q) htransported

end OptimalG
