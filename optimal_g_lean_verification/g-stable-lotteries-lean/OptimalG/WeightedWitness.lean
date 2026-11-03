import OptimalG.RegularRationalization

/-! # Actual finite distortion witnesses from regular weighted profiles -/

namespace OptimalG
open Set Filter MeasureTheory
open scoped BigOperators Topology

/-- Strictly violating regular profiles become actual equally weighted elections.
The IFT corrects the lottery exactly, and the strict metric violation persists. -/
theorem regular_weighted_violation_witness {V : Type*} [Fintype V] {m : ℕ} [NeZero m]
    (g : ℝ → ℝ) (hg : Continuous g) (orders : V → Equiv.Perm (Fin m))
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hwsum : ∑ v, w v = 1) (mean : ℝ)
    (hstationary : ∀ a, expectation w (fun v => scoreExtension g (orders v) a (uniformVector m)) = mean)
    (hregular : ∀ h : Fin m → ℝ, (∑ a, h a) = 0 →
      profileLotteryJacobian g orders w (uniformVector m) h = 0 → h = 0)
    (rho : Fin m → ℝ) (hrho : ∀ a, 0 ≤ rho a) (a : Fin m) (ha : rho a = 0)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hexcess : lam * expectation w (fun v => maximumGap (fun a => ((orders v).symm a).val) rho) <
      expectation w (fun v => expectation (uniformVector m)
        (runningMin (fun a => ((orders v).symm a).val) rho))) :
    WitnessAbove g (1 + 2 * lam) := by
  let gap := fun v => maximumGap (fun a => ((orders v).symm a).val) rho
  let minima := fun v => runningMin (fun a => ((orders v).symm a).val) rho
  let U : Set ((V → ℝ) × (Fin m → ℝ)) :=
    {p | lam * expectation p.1 gap < expectation p.1 (fun v => expectation p.2 (minima v))}
  have hleft : Continuous (fun p : (V → ℝ) × (Fin m → ℝ) => lam * expectation p.1 gap) := by
    unfold expectation
    fun_prop
  have hright : Continuous (fun p : (V → ℝ) × (Fin m → ℝ) =>
      expectation p.1 (fun v => expectation p.2 (minima v))) := by
    unfold expectation
    fun_prop
  have hU : U ∈ 𝓝 (w, uniformVector m) := (isOpen_lt hleft hright).mem_nhds hexcess
  obtain ⟨copies, hcopies, D, _hpositive, hmem, hstable⟩ :=
    exists_rational_stationary_near_regular g hg orders w hw hwsum mean hstationary hregular U hU
  exact replicatedElection_witnessAbove (NeZero.pos m) orders copies hcopies g D rho hrho a ha lam hlam
    (fun a => (hstable a).le) hmem

/-- Aggregate a weighted finite profile onto the finite set of all rankings. -/
noncomputable def rankingWeight {V : Type*} [Fintype V] {m : ℕ}
    (orders : V → Equiv.Perm (Fin m)) (w : V → ℝ) (order : Equiv.Perm (Fin m)) : ℝ :=
  ∑ v, if orders v = order then w v else 0

theorem rankingWeight_average {V : Type*} [Fintype V] {m : ℕ}
    (orders : V → Equiv.Perm (Fin m)) (w : V → ℝ) (f : Equiv.Perm (Fin m) → ℝ) :
    expectation (rankingWeight orders w) f = expectation w (fun v => f (orders v)) := by
  unfold expectation rankingWeight
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp [ite_mul]

theorem rankingWeight_nonneg {V : Type*} [Fintype V] {m : ℕ}
    (orders : V → Equiv.Perm (Fin m)) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∀ order, 0 ≤ rankingWeight orders w order := by
  intro order
  apply Finset.sum_nonneg
  intro v _
  split_ifs
  · exact hw v
  · rfl

theorem rankingWeight_total {V : Type*} [Fintype V] {m : ℕ}
    (orders : V → Equiv.Perm (Fin m)) (w : V → ℝ) (hwsum : ∑ v, w v = 1) :
    ∑ order, rankingWeight orders w order = 1 := by
  have h := rankingWeight_average orders w (fun _ => (1 : ℝ))
  simpa only [expectation, mul_one, hwsum] using h

theorem expectation_weight_affine {V : Type*} [Fintype V]
    (w z f : V → ℝ) (t : ℝ) :
    expectation (fun v => (1 - t) * w v + t * z v) f =
      (1 - t) * expectation w f + t * expectation z f := by
  unfold expectation
  simp only [add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

theorem profileLotteryJacobian_weight_affine {V : Type*} [Fintype V] {m : ℕ}
    (g : ℝ → ℝ) (orders : V → Equiv.Perm (Fin m)) (w z : V → ℝ)
    (D : Fin m → ℝ) (t : ℝ) :
    profileLotteryJacobian g orders (fun v => (1 - t) * w v + t * z v) D =
      (1 - t) • profileLotteryJacobian g orders w D + t • profileLotteryJacobian g orders z D := by
  ext h a
  simp only [profileLotteryJacobian_apply, add_apply, smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact expectation_weight_affine w z _ t

end OptimalG
