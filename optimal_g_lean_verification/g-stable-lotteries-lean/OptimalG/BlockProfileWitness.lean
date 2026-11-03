import OptimalG.ThreeClassWitness

/-! # Reusable finite block-profile witnesses, including auxiliary voter types -/

namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

/-- A finite family of high-class blocks yields an actual equal-voter witness
from exact class balance and strict reference stability. Per-type metric bounds
are explicit inputs, proved for the three main types in `TwoLevelBlocks` and
`TwoLevelGaps`; auxiliary types can use the universal bounds N≥0 and Δ≤2. -/
theorem block_profile_strict_witness {T : Type*} [Fintype T]
    (g : ℝ → ℝ) (hg : Continuous g) (lam : ℝ) (hlam : 0 ≤ lam)
    (z h n : ℕ) (hz : 0 < z) (hh : 0 < h) [NeZero (z + h)]
    (e : PairedSupport n ≃ Fin (z + h)) (a b c : Fin (z + h))
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (hstrength : cyclicStrength g a (1 / (z + h : ℕ)) ≠ 0)
    (starts : T → ℕ) (hstarts : ∀ t, starts t ≤ z) (positions : T → Fin (z + h + 1))
    (w : T → ℝ) (hw : ∀ t, 0 ≤ w t) (hwsum : ∑ t, w t = 1)
    (hbalance : expectation w (fun t => centeredPrimitive g ((starts t : ℝ) / (z + h : ℕ)) -
      centeredPrimitive g (((starts t + h : ℕ) : ℝ) / (z + h : ℕ))) = 0)
    (hreference : expectation w (fun t => g (((positions t).val : ℝ) / (z + h : ℕ))) < activationPrimitive g 1)
    (N G : T → ℝ)
    (hN : ∀ t (order : Equiv.Perm (Fin (z + h))),
      (∀ i, binaryHeight z (order i) = if i.val < starts t ∨ starts t + h ≤ i.val then 1 else 0) →
      N t ≤ expectation (extendZeroWeight (uniformVector (z + h)))
        (runningMin (fun a => ((insertReferenceOrder (positions t) order).symm a).val)
          (extendZeroWeight (twoLevelHeight z))))
    (hG : ∀ t (order : Equiv.Perm (Fin (z + h))),
      (∀ i, binaryHeight z (order i) = if i.val < starts t ∨ starts t + h ≤ i.val then 1 else 0) →
      maximumGap (fun a => ((insertReferenceOrder (positions t) order).symm a).val)
        (extendZeroWeight (twoLevelHeight z)) ≤ G t)
    (hexcess : lam * expectation w G < expectation w N) :
    WitnessAbove g (1 + 2 * lam) := by
  classical
  have hexists : ∀ t, ∃ order : Equiv.Perm (Fin (z + h)), ∀ i,
      binaryHeight z (order i) = if i.val < starts t ∨ starts t + h ≤ i.val then 1 else 0 :=
    fun t => exists_binary_block_order z h (starts t) (hstarts t)
  choose baseOrders hshape using hexists
  let Group := heightStabilizer (binaryHeight (m := z + h) z)
  let orders := classProfileOrder (binaryHeight z) baseOrders
  let pos := fun v : T × Group => positions v.1
  let weights := typeProfileWeight (G := Group) w
  have hs := class_block_stationary g hg z h hz hh starts hstarts baseOrders hshape w hwsum hbalance
  have hrefAvg : expectation weights (fun v =>
      g (rankCut (fun i => uniformVector (z + h) (orders v i)) (pos v).val)) < activationPrimitive g 1 := by
    rw [classProfile_reference_average]
    exact hreference
  have hNAvg : expectation w N ≤ expectation weights (fun v =>
      expectation (extendZeroWeight (uniformVector (z + h)))
        (runningMin (fun a => ((insertReferenceOrder (pos v) (orders v)).symm a).val)
          (extendZeroWeight (twoLevelHeight z)))) := by
    rw [← typeProfile_constant_average (G := Group) w N]
    apply expectation_mono (typeProfileWeight_nonneg w hw)
    intro v
    exact hN v.1 (orders v) (classProfile_block_shape z h starts baseOrders hshape v)
  have hGAvg : expectation weights (fun v =>
      maximumGap (fun a => ((insertReferenceOrder (pos v) (orders v)).symm a).val)
        (extendZeroWeight (twoLevelHeight z))) ≤ expectation w G := by
    rw [← typeProfile_constant_average (G := Group) w G]
    apply expectation_mono (typeProfileWeight_nonneg w hw)
    intro v
    exact hG v.1 (orders v) (classProfile_block_shape z h starts baseOrders hshape v)
  apply one_reference_equal_voter_realization g hg e a b c hab hbc hstrength orders pos weights
    (typeProfileWeight_nonneg w hw) (typeProfileWeight_total w hwsum) hs hrefAvg
    (extendZeroWeight (twoLevelHeight z)) (extendZeroWeight_nonneg _ (twoLevelHeight_nonneg z)) (by simp)
    lam hlam
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hGAvg hlam) (lt_of_lt_of_le hexcess hNAvg)

theorem twoLevel_cost_nonneg (z h : ℕ) [NeZero (z + h)]
    (order : Equiv.Perm (Fin (z + h))) (k : Fin (z + h + 1)) :
    0 ≤ expectation (extendZeroWeight (uniformVector (z + h)))
      (runningMin (fun a => ((insertReferenceOrder k order).symm a).val)
        (extendZeroWeight (twoLevelHeight z))) := by
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg
  · exact extendZeroWeight_nonneg _ (fun _ => one_div_nonneg.mpr (Nat.cast_nonneg _)) a
  · exact runningMin_nonneg _ _ (extendZeroWeight_nonneg _ (twoLevelHeight_nonneg z)) a

end OptimalG
