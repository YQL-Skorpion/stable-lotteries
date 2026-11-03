import OptimalG.OneReferenceOrder
import OptimalG.WeightedWitness

/-! # Exact equal-voter witnesses with one strictly stable unsupported reference -/

namespace OptimalG
open Set Filter MeasureTheory
open scoped BigOperators Topology

theorem extendZeroWeight_continuous {m : ℕ} :
    Continuous (extendZeroWeight (m := m)) := by
  apply continuous_pi
  intro a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simpa only [extendZeroWeight_last] using (continuous_const : Continuous (fun _ : Fin m → ℝ => (0 : ℝ)))
  · simpa only [extendZeroWeight_castSucc] using (continuous_apply i : Continuous (fun D : Fin m → ℝ => D i))

theorem referenceScore_continuous {m : ℕ} (g : ℝ → ℝ) (hg : Continuous g)
    (k : Fin (m + 1)) (order : Equiv.Perm (Fin m)) :
    Continuous (fun D : Fin m → ℝ => g (rankCut (fun i => D (order i)) k.val)) := by
  apply hg.comp
  unfold rankCut
  apply continuous_finsetSum
  intro i _
  split_ifs <;> fun_prop

/-- The implicit correction involves only supported scores. The unsupported
reference inequality and the metric violation are preserved as open conditions. -/
theorem regular_one_reference_witness {V : Type*} [Fintype V] {m : ℕ} [NeZero m]
    (g : ℝ → ℝ) (hg : Continuous g)
    (orders : V → Equiv.Perm (Fin m)) (positions : V → Fin (m + 1))
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hwsum : ∑ v, w v = 1)
    (hstationary : ∀ a, expectation w (fun v => scoreExtension g (orders v) a (uniformVector m)) =
      activationPrimitive g 1)
    (hregular : ∀ h : Fin m → ℝ, (∑ a, h a) = 0 →
      profileLotteryJacobian g orders w (uniformVector m) h = 0 → h = 0)
    (hreference : expectation w (fun v =>
      g (rankCut (fun i => uniformVector m (orders v i)) (positions v).val)) < activationPrimitive g 1)
    (rho : Fin (m + 1) → ℝ) (hrho : ∀ a, 0 ≤ rho a) (href : rho (Fin.last m) = 0)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hexcess : lam * expectation w (fun v =>
        maximumGap (fun a => ((insertReferenceOrder (positions v) (orders v)).symm a).val) rho) <
      expectation w (fun v => expectation (extendZeroWeight (uniformVector m))
        (runningMin (fun a => ((insertReferenceOrder (positions v) (orders v)).symm a).val) rho))) :
    WitnessAbove g (1 + 2 * lam) := by
  let fullOrders := fun v => insertReferenceOrder (positions v) (orders v)
  let gap := fun v => maximumGap (fun a => ((fullOrders v).symm a).val) rho
  let minima := fun v => runningMin (fun a => ((fullOrders v).symm a).val) rho
  let refScore := fun (p : (V → ℝ) × (Fin m → ℝ)) => expectation p.1
    (fun v => g (rankCut (fun i => p.2 (orders v i)) (positions v).val))
  let cost := fun (p : (V → ℝ) × (Fin m → ℝ)) =>
    expectation p.1 (fun v => expectation (extendZeroWeight p.2) (minima v))
  have hreferenceCont : Continuous refScore := by
    unfold refScore expectation
    apply continuous_finsetSum
    intro v _
    exact ((continuous_apply v).comp continuous_fst).mul
      ((referenceScore_continuous g hg (positions v) (orders v)).comp continuous_snd)
  have hcostCont : Continuous cost := by
    unfold cost expectation
    apply continuous_finsetSum
    intro v _
    apply ((continuous_apply v).comp continuous_fst).mul
    apply continuous_finsetSum
    intro a _
    exact (((continuous_apply a).comp extendZeroWeight_continuous).comp continuous_snd).mul continuous_const
  have hgapCont : Continuous (fun p : (V → ℝ) × (Fin m → ℝ) => lam * expectation p.1 gap) := by
    unfold expectation
    fun_prop
  let U : Set ((V → ℝ) × (Fin m → ℝ)) :=
    {p | refScore p < activationPrimitive g 1 ∧ lam * expectation p.1 gap < cost p}
  have hU : U ∈ 𝓝 (w, uniformVector m) := by
    apply Filter.inter_mem
    · apply (isOpen_lt hreferenceCont continuous_const).mem_nhds
      exact hreference
    · apply (isOpen_lt hgapCont hcostCont).mem_nhds
      exact hexcess
  obtain ⟨copies, hcopies, D, _hpositive, hmem, hstable⟩ :=
    exists_rational_stationary_near_regular g hg orders w hw hwsum (activationPrimitive g 1)
      hstationary hregular U hU
  apply replicatedElection_witnessAbove (by omega : 0 < m + 1) fullOrders copies hcopies g (extendZeroLottery D)
    rho hrho (Fin.last m) href lam hlam _ hmem.2
  intro a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · change expectation (copyWeight copies) (fun v =>
      orderedActivation g (extendZeroWeight D.weight) (fullOrders v) (Fin.last m)) ≤ _
    dsimp only [fullOrders]
    simp_rw [insertReference_reference_activation]
    exact hmem.1.le
  · change expectation (copyWeight copies) (fun v =>
      orderedActivation g (extendZeroWeight D.weight) (fullOrders v) i.castSucc) ≤ _
    dsimp only [fullOrders]
    simp_rw [insertReference_supported_activation]
    exact (hstable i).le

end OptimalG
