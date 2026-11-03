import OptimalG.OneReferenceWitness
import OptimalG.EqualVoterRealization

/-! # Equal-voter realization with a strictly stable unsupported candidate -/

namespace OptimalG
open Set Filter MeasureTheory
open scoped BigOperators Topology

theorem expectation_sum_left {V W : Type*} [Fintype V] [Fintype W]
    (w : V → ℝ) (f : V ⊕ W → ℝ) :
    expectation (Sum.elim w (fun _ => 0)) f = expectation w (fun v => f (Sum.inl v)) := by
  simp [expectation, Fintype.sum_sum_type]

theorem expectation_sum_right {V W : Type*} [Fintype V] [Fintype W]
    (w : W → ℝ) (f : V ⊕ W → ℝ) :
    expectation (Sum.elim (fun _ => 0) w) f = expectation w (fun v => f (Sum.inr v)) := by
  simp [expectation, Fintype.sum_sum_type]

/-- Actual finite weighted profiles with one strictly stable zero-mass
reference admit exact finite equal-voter distortion witnesses. The auxiliary
profile need not make that reference stable: sufficiently small mixing retains
the original strict reference margin. -/
theorem one_reference_equal_voter_realization {V : Type*} [Fintype V] {n m : ℕ} [NeZero m]
    (g : ℝ → ℝ) (hg : Continuous g)
    (e : PairedSupport n ≃ Fin m) (a b c : Fin m)
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (hstrength : cyclicStrength g a (1 / (m : ℝ)) ≠ 0)
    (orders : V → Equiv.Perm (Fin m)) (positions : V → Fin (m + 1))
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hwsum : ∑ v, w v = 1)
    (hstationary : ∀ a, expectation w (fun v => orderedActivation g (uniformVector m) (orders v) a) =
      activationPrimitive g 1)
    (hreference : expectation w (fun v =>
      g (rankCut (fun i => uniformVector m (orders v i)) (positions v).val)) < activationPrimitive g 1)
    (rho : Fin (m + 1) → ℝ) (hrho : ∀ x, 0 ≤ rho x) (href : rho (Fin.last m) = 0)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hexcess : lam * expectation w (fun v =>
        maximumGap (fun x => ((insertReferenceOrder (positions v) (orders v)).symm x).val) rho) <
      expectation w (fun v => expectation (extendZeroWeight (uniformVector m))
        (runningMin (fun x => ((insertReferenceOrder (positions v) (orders v)).symm x).val) rho))) :
    WitnessAbove g (1 + 2 * lam) := by
  classical
  let P := Equiv.Perm (Fin m)
  let mean := activationPrimitive g 1
  let u := 1 / (m : ℝ)
  have hu : u ≠ 0 := one_div_ne_zero (by exact_mod_cast NeZero.ne m)
  obtain ⟨wAux, hwAux, hsumAux, hsAux, hregAux⟩ :=
    exists_regular_auxiliary_profile g hg e a b c hab hbc hstrength
  let os : V ⊕ P → P := Sum.elim orders id
  let ks : V ⊕ P → Fin (m + 1) := Sum.elim positions (fun _ => 0)
  let w0 : V ⊕ P → ℝ := Sum.elim w (fun _ => 0)
  let w1 : V ⊕ P → ℝ := Sum.elim (fun _ => 0) wAux
  have hw0 : ∀ v, 0 ≤ w0 v := by intro v; cases v <;> simp [w0, hw]
  have hw1 : ∀ v, 0 ≤ w1 v := by
    intro v
    cases v with
    | inl v => simp [w1]
    | inr p => exact (hwAux p).le
  have hsum0 : ∑ v, w0 v = 1 := by simpa [w0, Fintype.sum_sum_type] using hwsum
  have hsum1 : ∑ v, w1 v = 1 := by simpa [w1, Fintype.sum_sum_type] using hsumAux
  have hs0 : ∀ x, expectation w0 (fun v => scoreExtension g (os v) x (uniformVector m)) = mean := by
    intro x
    rw [expectation_sum_left]
    simp_rw [scoreExtension_eq_orderedActivation g hg _ _ (uniformVector m) hu]
    exact hstationary x
  have hs1 : ∀ x, expectation w1 (fun v => scoreExtension g (os v) x (uniformVector m)) = mean := by
    intro x
    rw [expectation_sum_right]
    exact hsAux x
  have hreg1 : ∀ h : Fin m → ℝ, (∑ x, h x) = 0 →
      profileLotteryJacobian g os w1 (uniformVector m) h = 0 → h = 0 := by
    intro h hsum hz
    apply hregAux h hsum
    ext x
    have he := congrFun hz x
    rw [profileLotteryJacobian_apply, expectation_sum_right] at he
    rw [profileLotteryJacobian_apply]
    exact he
  let A := (profileTangentJacobian g os w0 u mean hu hs0).toContinuousLinearMap
  let B := (profileTangentJacobian g os w1 u mean hu hs1).toContinuousLinearMap
  have hB : B.IsInvertible := profileTangentJacobian_isInvertible g os w1 u mean hu hs1 hreg1
  let mix := fun t v => (1 - t) * w0 v + t * w1 v
  let fullOrders := fun v => insertReferenceOrder (ks v) (os v)
  let gap := fun v => maximumGap (fun x => ((fullOrders v).symm x).val) rho
  let cost := fun v => expectation (extendZeroWeight (uniformVector m))
    (runningMin (fun x => ((fullOrders v).symm x).val) rho)
  let refScore := fun v => g (rankCut (fun i => uniformVector m (os v i)) (ks v).val)
  have hexcess0 : lam * expectation w0 gap < expectation w0 cost := by
    rw [expectation_sum_left, expectation_sum_left]
    exact hexcess
  have href0 : expectation w0 refScore < mean := by
    rw [expectation_sum_left]
    exact hreference
  have hleft : Continuous (fun t : ℝ => lam * expectation (mix t) gap) := by unfold expectation mix; fun_prop
  have hright : Continuous (fun t : ℝ => expectation (mix t) cost) := by unfold expectation mix; fun_prop
  have hrefcont : Continuous (fun t : ℝ => expectation (mix t) refScore) := by unfold expectation mix; fun_prop
  let U : Set ℝ := {t | t < 1 ∧ expectation (mix t) refScore < mean ∧
    lam * expectation (mix t) gap < expectation (mix t) cost}
  have hU : U ∈ 𝓝 0 := by
    apply Filter.inter_mem
    · exact (isOpen_lt continuous_id continuous_const).mem_nhds (show (0 : ℝ) < 1 by norm_num)
    apply Filter.inter_mem
    · apply (isOpen_lt hrefcont continuous_const).mem_nhds
      change expectation (mix 0) refScore < mean
      simpa only [mix, sub_zero, one_mul, zero_mul, add_zero] using href0
    · apply (isOpen_lt hleft hright).mem_nhds
      change lam * expectation (mix 0) gap < expectation (mix 0) cost
      simpa only [mix, sub_zero, one_mul, zero_mul, add_zero] using hexcess0
  obtain ⟨t, ht, hmem, hregular⟩ := operator_regular_mixture_mem_nhds A B hB U hU
  have hnonneg : ∀ v, 0 ≤ mix t v := fun v =>
    add_nonneg (mul_nonneg (sub_nonneg.mpr hmem.1.le) (hw0 v)) (mul_nonneg ht.le (hw1 v))
  have htotal : ∑ v, mix t v = 1 := by
    dsimp [mix]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum0, hsum1]
    ring
  have hs : ∀ x, expectation (mix t) (fun v => scoreExtension g (os v) x (uniformVector m)) = mean := by
    intro x
    rw [expectation_weight_affine, hs0, hs1]
    ring
  have hJac : (profileTangentJacobian g os (mix t) u mean hu hs).toContinuousLinearMap =
      (1 - t) • A + t • B := by
    apply ContinuousLinearMap.ext
    intro h
    apply Subtype.ext
    change profileLotteryJacobian g os (mix t) (uniformVector m) h.val = _
    rw [profileLotteryJacobian_weight_affine]
    rfl
  have hinj : ∀ h : Fin m → ℝ, (∑ x, h x) = 0 →
      profileLotteryJacobian g os (mix t) (uniformVector m) h = 0 → h = 0 := by
    intro h hsum hz
    let hT : probabilityTangent (Fin m) := ⟨h, hsum⟩
    have hzeroT : (profileTangentJacobian g os (mix t) u mean hu hs).toContinuousLinearMap hT = 0 := by
      apply Subtype.ext
      exact hz
    have hregT : (profileTangentJacobian g os (mix t) u mean hu hs).toContinuousLinearMap.IsInvertible := by
      rw [hJac]
      exact hregular
    have hTzero : hT = 0 := hregT.injective (hzeroT.trans (map_zero _).symm)
    exact congrArg Subtype.val hTzero
  exact regular_one_reference_witness g hg os ks (mix t) hnonneg htotal hs hinj
    hmem.2.1 rho hrho href lam hlam hmem.2.2

end OptimalG
