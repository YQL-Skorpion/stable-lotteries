import OptimalG.SignedProfile
import OptimalG.AuxiliarySkew

/-!
# A finite signed profile realizing the full odd-support skew operator

Every paired triple is realized by six actual rankings. The finite sum of their
signed ranking weights preserves all scores at the uniform lottery, and its
actual derivative is the invertible skew operator on the probability tangent.
-/

namespace OptimalG
open scoped BigOperators

/-- Assemble the local cyclic profiles into the full paired-support perturbation. -/
theorem exists_paired_skew_profile {n m : ℕ} (g : ℝ → ℝ)
    (e : PairedSupport n ≃ Fin m) (a b c : Fin m)
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (u : ℝ) (hu : u ≠ 0) :
    ∃ W : Equiv.Perm (Fin m) → ℝ,
      (∑ order, W order) = 0 ∧
      (∀ x, expectation W (fun order => orderedActivation g (fun _ => u) order x) = 0) ∧
      (∀ (h : Fin m → ℝ) (q : PairedSupport n),
        expectation W (fun order => scoreDerivative g order (e q) (fun _ => u) h) =
          pairedSkew n (cyclicStrength g a u) (fun q => h (e q)) q) := by
  let base := e none
  let left := fun i : Fin n => e (some (Sum.inl i))
  let right := fun i : Fin n => e (some (Sum.inr i))
  have hbl (i : Fin n) : base ≠ left i := by
    intro h; have hh := e.injective h; cases hh
  have hbr (i : Fin n) : base ≠ right i := by
    intro h; have hh := e.injective h; cases hh
  have hlr (i j : Fin n) : left i ≠ right j := by
    intro h; have hh := e.injective h; cases hh
  have hll : Function.Injective left := by
    intro i j hij
    have h := e.injective hij
    simpa only [Option.some.injEq, Sum.inl.injEq] using h
  have hrr : Function.Injective right := by
    intro i j hij
    have h := e.injective hij
    simpa only [Option.some.injEq, Sum.inr.injEq] using h
  have hlocal (i : Fin n) := exists_cyclic_profile g a b c hab hbc
    base (left i) (right i) (hbl i) (hbr i) (hlr i i) u hu
  choose orders hstationary hbase hleft hright houtside using hlocal
  let W : Equiv.Perm (Fin m) → ℝ := fun order => ∑ i, signedRankingWeight (orders i) order
  have haverage (f : Equiv.Perm (Fin m) → ℝ) :
      expectation W f = ∑ i, signedSix (fun j => f (orders i j)) := by
    unfold expectation W
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact signedRankingWeight_average (orders i) f
  refine ⟨W, ?_, ?_, ?_⟩
  · unfold W
    rw [Finset.sum_comm]
    simp only [signedRankingWeight_total, Finset.sum_const_zero]
  · intro x
    rw [haverage]
    simp only [hstationary, Finset.sum_const_zero]
  · intro h q
    rw [haverage]
    rcases q with _ | (i | i)
    · change (∑ j, signedSix (fun k => scoreDerivative g (orders j k) base (fun _ => u) h)) = _
      simp only [hbase, pairedSkew, ← Finset.mul_sum]
      rfl
    · change (∑ j, signedSix (fun k => scoreDerivative g (orders j k) (left i) (fun _ => u) h)) = _
      rw [Finset.sum_eq_single i]
      · exact hleft i h
      · intro j _ hji
        apply houtside j (left i) (Ne.symm (hbl i))
        · exact fun hh => hji (hll hh).symm
        · exact hlr i j
      · simp
    · change (∑ j, signedSix (fun k => scoreDerivative g (orders j k) (right i) (fun _ => u) h)) = _
      rw [Finset.sum_eq_single i]
      · exact hright i h
      · intro j _ hji
        apply houtside j (right i) (Ne.symm (hbr i))
        · exact Ne.symm (hlr j i)
        · exact fun hh => hji (hrr hh).symm
      · simp

end OptimalG
