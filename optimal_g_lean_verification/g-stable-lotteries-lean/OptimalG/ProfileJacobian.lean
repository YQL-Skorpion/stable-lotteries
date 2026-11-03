import OptimalG.ScoreDerivative
import OptimalG.ScoreRelabel
import OptimalG.AuxiliarySkew

/-!
# The finite profile Jacobian and its probability-tangent restriction

The derivative of the rank partition is checked by a finite telescoping sum.
At a stationary uniform lottery this forces the score derivative to map the
zero-sum lottery tangent space into itself.
-/

namespace OptimalG
open scoped BigOperators

/-- Product-rule identity for one actual rank-interval score. -/
theorem scoreDerivative_product_rule {m : ℕ} (g : ℝ → ℝ)
    (order : Equiv.Perm (Fin m)) (D h : Fin m → ℝ) (a : Fin m) (hDa : D a ≠ 0) :
    D a * scoreDerivative g order a D h + scoreExtension g order a D * h a =
      g (rankPrefixLinear order a D + D a) * (rankPrefixLinear order a h + h a) -
        g (rankPrefixLinear order a D) * rankPrefixLinear order a h := by
  rw [scoreDerivative_apply g order a D h hDa]
  field_simp
  ring

/-- Differentiating the partition identity gives this exact finite telescoping
formula, valid for arbitrary nonzero masses and all variation vectors. -/
theorem scoreDerivative_partition {m : ℕ} (g : ℝ → ℝ)
    (order : Equiv.Perm (Fin m)) (D h : Fin m → ℝ) (hD : ∀ a, D a ≠ 0) :
    (∑ a, (D a * scoreDerivative g order a D h + scoreExtension g order a D * h a)) =
      g (∑ a, D a) * ∑ a, h a := by
  let F := fun k => g (rankCut (fun i => D (order i)) k) * rankCut (fun i => h (order i)) k
  have hterm (i : Fin m) :
      D (order i) * scoreDerivative g order (order i) D h +
        scoreExtension g order (order i) D * h (order i) = F (i.val + 1) - F i.val := by
    rw [scoreDerivative_product_rule g order D h (order i) (hD (order i))]
    simp only [rankPrefixLinear_apply, Equiv.symm_apply_apply]
    dsimp only [F]
    rw [rankCut_succ, rankCut_succ]
  calc
    _ = ∑ i : Fin m, (D (order i) * scoreDerivative g order (order i) D h +
        scoreExtension g order (order i) D * h (order i)) := (Equiv.sum_comp order _).symm
    _ = ∑ i : Fin m, (F (i.val + 1) - F i.val) := Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ∑ i ∈ Finset.range m, (F (i + 1) - F i) := Fin.sum_univ_eq_sum_range (fun i : ℕ => F (i + 1) - F i) m
    _ = F m - F 0 := by
      have ht := Finset.sum_range_sub' F m
      simp only [Finset.sum_sub_distrib] at ht ⊢
      linarith
    _ = _ := by simp [F, rankCut, Equiv.sum_comp]

noncomputable def profileLotteryJacobian {V : Type*} [Fintype V] {m : ℕ}
    (g : ℝ → ℝ) (orders : V → Equiv.Perm (Fin m)) (w : V → ℝ) (D : Fin m → ℝ) :
    (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi (fun a => ∑ v, w v • scoreDerivative g (orders v) a D)

theorem profileLotteryJacobian_apply {V : Type*} [Fintype V] {m : ℕ}
    (g : ℝ → ℝ) (orders : V → Equiv.Perm (Fin m)) (w : V → ℝ) (D h : Fin m → ℝ) (a : Fin m) :
    profileLotteryJacobian g orders w D h a = expectation w (fun v => scoreDerivative g (orders v) a D h) := by
  simp [profileLotteryJacobian, expectation]

/-- Actual strict derivative of the complete profile score vector. -/
theorem profileScore_hasStrictFDerivAt {V : Type*} [Fintype V] {m : ℕ}
    (g : ℝ → ℝ) (hg : Continuous g) (orders : V → Equiv.Perm (Fin m))
    (w : V → ℝ) (D : Fin m → ℝ) (hD : ∀ a, D a ≠ 0) :
    HasStrictFDerivAt (fun D a => expectation w (fun v => scoreExtension g (orders v) a D))
      (profileLotteryJacobian g orders w D) D := by
  apply hasStrictFDerivAt_pi.mpr
  intro a
  apply HasStrictFDerivAt.fun_sum
  intro v _
  convert! (scoreExtension_hasStrictFDerivAt g hg (orders v) a D (hD a)).const_smul (w v) using 1

/-- Every stationary profile Jacobian maps the simplex tangent into itself. -/
theorem profileLotteryJacobian_maps_tangent {V : Type*} [Fintype V] {m : ℕ}
    (g : ℝ → ℝ) (orders : V → Equiv.Perm (Fin m)) (w : V → ℝ)
    (u mean : ℝ) (hu : u ≠ 0)
    (hstationary : ∀ a, expectation w (fun v => scoreExtension g (orders v) a (fun _ => u)) = mean)
    (h : Fin m → ℝ) (hsum : ∑ a, h a = 0) :
    ∑ a, profileLotteryJacobian g orders w (fun _ => u) h a = 0 := by
  have hpart (v : V) := scoreDerivative_partition g (orders v) (fun _ : Fin m => u) h (fun _ => hu)
  have hzero : expectation w (fun v => ∑ a, (u * scoreDerivative g (orders v) a (fun _ => u) h +
      scoreExtension g (orders v) a (fun _ => u) * h a)) = 0 := by
    simp_rw [hpart, hsum, mul_zero]
    simp [expectation]
  have hexpand : expectation w (fun v => ∑ a, (u * scoreDerivative g (orders v) a (fun _ => u) h +
      scoreExtension g (orders v) a (fun _ => u) * h a)) =
      u * (∑ a, profileLotteryJacobian g orders w (fun _ => u) h a) + mean * ∑ a, h a := by
    unfold expectation
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · simp only [profileLotteryJacobian_apply, expectation]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    · apply Finset.sum_congr rfl
      intro a _
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      change expectation w (fun v => scoreExtension g (orders v) a (fun _ => u)) * h a = mean * h a
      rw [hstationary]
  rw [hexpand, hsum, mul_zero, add_zero] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left hu

end OptimalG
