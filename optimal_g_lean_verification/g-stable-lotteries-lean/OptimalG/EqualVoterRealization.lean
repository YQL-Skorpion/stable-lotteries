import OptimalG.RegularAuxiliaryProfile
import OptimalG.WeightedWitness
import OptimalG.RegularMixture

/-!
# Equal-voter realization for full-support weighted elections

This composes the actual auxiliary profile, small nonsingular mixtures, the
actual score IFT, exact rational replication, and the biased-metric realization.
The only grid hypothesis is a nonzero interior adjacent activation difference;
`InteriorGrid` proves it for every sufficiently fine nonconstant activation.
-/

namespace OptimalG
open Set Filter MeasureTheory
open scoped BigOperators Topology

/-- Appendix A.1 for full support: every strict weighted violation at a uniform
odd-support lottery yields an actual finite equal-voter distortion witness. -/
theorem full_support_equal_voter_realization {V : Type*} [Fintype V] {n m : ℕ} [NeZero m]
    (g : ℝ → ℝ) (hg : Continuous g)
    (e : PairedSupport n ≃ Fin m) (a b c : Fin m)
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (hstrength : cyclicStrength g a (1 / (m : ℝ)) ≠ 0)
    (orders : V → Equiv.Perm (Fin m)) (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hwsum : ∑ v, w v = 1)
    (hstationary : ∀ x, expectation w (fun v => scoreExtension g (orders v) x (uniformVector m)) =
      ∫ r in (0 : ℝ)..1, g r)
    (rho : Fin m → ℝ) (hrho : ∀ x, 0 ≤ rho x) (reference : Fin m) (href : rho reference = 0)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hexcess : lam * expectation w (fun v => maximumGap (fun x => ((orders v).symm x).val) rho) <
      expectation w (fun v => expectation (uniformVector m)
        (runningMin (fun x => ((orders v).symm x).val) rho))) :
    WitnessAbove g (1 + 2 * lam) := by
  let P := Equiv.Perm (Fin m)
  let mean := ∫ r in (0 : ℝ)..1, g r
  let u := 1 / (m : ℝ)
  have hu : u ≠ 0 := one_div_ne_zero (by exact_mod_cast NeZero.ne m)
  let w0 := rankingWeight orders w
  have hw0 : ∀ order, 0 ≤ w0 order := rankingWeight_nonneg orders w hw
  have hsum0 : ∑ order, w0 order = 1 := rankingWeight_total orders w hwsum
  have hs0 : ∀ x, expectation w0 (fun order => scoreExtension g order x (uniformVector m)) = mean := by
    intro x
    rw [rankingWeight_average]
    exact hstationary x
  obtain ⟨w1, hw1, hsum1, hs1, hreg1⟩ := exists_regular_auxiliary_profile g hg e a b c hab hbc hstrength
  let A := (profileTangentJacobian g (id : P → P) w0 u mean hu hs0).toContinuousLinearMap
  let B := (profileTangentJacobian g (id : P → P) w1 u mean hu hs1).toContinuousLinearMap
  have hB : B.IsInvertible := profileTangentJacobian_isInvertible g id w1 u mean hu hs1 hreg1
  let mix := fun t order => (1 - t) * w0 order + t * w1 order
  let gap := fun order : P => maximumGap (fun x => (order.symm x).val) rho
  let cost := fun order : P => expectation (uniformVector m) (runningMin (fun x => (order.symm x).val) rho)
  have hexcess0 : lam * expectation w0 gap < expectation w0 cost := by
    rw [rankingWeight_average, rankingWeight_average]
    exact hexcess
  have hleft : Continuous (fun t : ℝ => lam * expectation (mix t) gap) := by
    unfold expectation mix
    fun_prop
  have hright : Continuous (fun t : ℝ => expectation (mix t) cost) := by
    unfold expectation mix
    fun_prop
  let U : Set ℝ := {t | t < 1 ∧ lam * expectation (mix t) gap < expectation (mix t) cost}
  have hU : U ∈ 𝓝 0 := by
    apply Filter.inter_mem
    · exact (isOpen_lt continuous_id continuous_const).mem_nhds (show (0 : ℝ) < 1 by norm_num)
    · apply (isOpen_lt hleft hright).mem_nhds
      change lam * expectation (mix 0) gap < expectation (mix 0) cost
      simpa only [mix, sub_zero, one_mul, zero_mul, add_zero] using hexcess0
  obtain ⟨t, ht, hmem, hregular⟩ := operator_regular_mixture_mem_nhds A B hB U hU
  have hnonneg : ∀ order, 0 ≤ mix t order := by
    intro order
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hmem.1.le) (hw0 order))
      (mul_nonneg ht.le (hw1 order).le)
  have htotal : ∑ order, mix t order = 1 := by
    dsimp [mix]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum0, hsum1]
    ring
  have hs : ∀ x, expectation (mix t) (fun order => scoreExtension g order x (uniformVector m)) = mean := by
    intro x
    rw [expectation_weight_affine, hs0]
    change (1 - t) * mean + t * expectation w1 (fun order => scoreExtension g order x (fun _ => 1 / (m : ℝ))) = mean
    rw [hs1]
    ring
  have hJac : (profileTangentJacobian g (id : P → P) (mix t) u mean hu hs).toContinuousLinearMap =
      (1 - t) • A + t • B := by
    apply ContinuousLinearMap.ext
    intro h
    apply Subtype.ext
    change profileLotteryJacobian g id (mix t) (uniformVector m) h.val = _
    rw [profileLotteryJacobian_weight_affine]
    rfl
  have hinj : ∀ h : Fin m → ℝ, (∑ x, h x) = 0 →
      profileLotteryJacobian g id (mix t) (uniformVector m) h = 0 → h = 0 := by
    intro h hsum hz
    let hT : probabilityTangent (Fin m) := ⟨h, hsum⟩
    have hzeroT : (profileTangentJacobian g (id : P → P) (mix t) u mean hu hs).toContinuousLinearMap hT = 0 := by
      apply Subtype.ext
      exact hz
    have hregT : (profileTangentJacobian g (id : P → P) (mix t) u mean hu hs).toContinuousLinearMap.IsInvertible := by
      rw [hJac]
      exact hregular
    have hTzero : hT = 0 := hregT.injective (hzeroT.trans (map_zero _).symm)
    exact congrArg Subtype.val hTzero
  exact regular_weighted_violation_witness g hg id (mix t) hnonneg htotal mean hs hinj
    rho hrho reference href lam hlam hmem.2

end OptimalG
