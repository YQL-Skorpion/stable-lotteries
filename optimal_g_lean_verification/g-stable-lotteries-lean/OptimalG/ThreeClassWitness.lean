import OptimalG.ThreeClassProfile

/-! # Actual finite-grid three-class distortion witnesses -/

namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

theorem typeProfile_constant_average {T G : Type*} [Fintype T] [Fintype G] [Nonempty G]
    (w : T → ℝ) (f : T → ℝ) :
    expectation (typeProfileWeight (G := G) w) (fun v => f v.1) = expectation w f := by
  rw [typeProfile_average]
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  congr 1
  funext t
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The three rank patterns have exactly the paper's centered class scores,
reference scores, running-minimum costs and maximum gaps. Strict reference
stability is retained in the equal-voter conversion. -/
theorem three_class_grid_strict_witness (g : ℝ → ℝ) (hg : Continuous g)
    (lam : ℝ) (hlam : 0 ≤ lam) (z h x y j n : ℕ)
    (hz : 0 < z) (hh : 0 < h) (hx : x ≤ z) (hyh : h ≤ y) (hym : y < z + h)
    (hjh : h < j) (hjm : j ≤ z + h) [NeZero (z + h)]
    (e : PairedSupport n ≃ Fin (z + h)) (a b c : Fin (z + h))
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (hstrength : cyclicStrength g a (1 / (z + h : ℕ)) ≠ 0)
    (w : Fin 3 → ℝ) (hw : ∀ t, 0 ≤ w t) (hwsum : ∑ t, w t = 1)
    (hbalance : expectation w ![centeredPrimitive g ((z : ℝ) / (z + h : ℕ)),
      centeredPrimitive g (((j - h : ℕ) : ℝ) / (z + h : ℕ)) - centeredPrimitive g ((j : ℝ) / (z + h : ℕ)),
      -centeredPrimitive g ((h : ℝ) / (z + h : ℕ))] = 0)
    (hreference : expectation w ![g ((x : ℝ) / (z + h : ℕ)), g ((j : ℝ) / (z + h : ℕ)),
      g ((y : ℝ) / (z + h : ℕ))] < activationPrimitive g 1)
    (hexcess : lam * expectation w ![2, 1, 1] <
      expectation w ![(x : ℝ) / (z + h : ℕ), (j : ℝ) / (z + h : ℕ),
        ((h : ℝ) + y) / (z + h : ℕ)]) :
    WitnessAbove g (1 + 2 * lam) := by
  classical
  let m := z + h
  let G := heightStabilizer (binaryHeight (m := m) z)
  let starts : Fin 3 → ℕ := ![z, j - h, 0]
  let positions : Fin 3 → Fin (m + 1) := ![⟨x, by dsimp [m]; omega⟩,
    ⟨j, by dsimp [m]; omega⟩, ⟨y, by dsimp [m]; omega⟩]
  have hstarts : ∀ t, starts t ≤ z := by intro t; fin_cases t <;> dsimp [starts] <;> omega
  have hexists : ∀ t, ∃ order : Equiv.Perm (Fin m), ∀ i,
      binaryHeight z (order i) = if i.val < starts t ∨ starts t + h ≤ i.val then 1 else 0 :=
    fun t => exists_binary_block_order z h (starts t) (hstarts t)
  choose baseOrders hshape using hexists
  let orders := classProfileOrder (binaryHeight z) baseOrders
  let pos := fun v : Fin 3 × G => positions v.1
  have hbalance' : expectation w (fun t => centeredPrimitive g ((starts t : ℝ) / m) -
      centeredPrimitive g (((starts t + h : ℕ) : ℝ) / m)) = 0 := by
    have hm : (m : ℝ) ≠ 0 := by dsimp [m]; positivity
    have heq : (fun t => centeredPrimitive g ((starts t : ℝ) / m) -
        centeredPrimitive g (((starts t + h : ℕ) : ℝ) / m)) =
        ![centeredPrimitive g ((z : ℝ) / m),
          centeredPrimitive g (((j - h : ℕ) : ℝ) / m) - centeredPrimitive g ((j : ℝ) / m),
          -centeredPrimitive g ((h : ℝ) / m)] := by
      funext t
      fin_cases t
      · dsimp [starts]
        have hm' : ((z + h : ℕ) : ℝ) / m = 1 := div_self hm
        rw [hm']
        simp [centeredPrimitive]
      · dsimp [starts]
        rw [Nat.sub_add_cancel hjh.le]
      · dsimp [starts]
        simp [centeredPrimitive, activationPrimitive]
    rw [heq]
    exact hbalance
  have hs := class_block_stationary g hg z h hz hh starts hstarts baseOrders hshape w hwsum hbalance'
  have hrefAvg : expectation (typeProfileWeight (G := G) w) (fun v =>
      g (rankCut (fun i => uniformVector m (orders v i)) (pos v).val)) < activationPrimitive g 1 := by
    rw [classProfile_reference_average]
    convert hreference using 1
    congr 1
    funext t
    fin_cases t <;> rfl
  have hcost : ∀ v : Fin 3 × G,
      expectation (extendZeroWeight (uniformVector m))
        (runningMin (fun a => ((insertReferenceOrder (pos v) (orders v)).symm a).val)
          (extendZeroWeight (twoLevelHeight z))) =
        ![(x : ℝ) / m, (j : ℝ) / m, ((h : ℝ) + y) / m] v.1 := by
    intro v
    rcases v with ⟨t, sigma⟩
    have hsh := classProfile_block_shape z h starts baseOrders hshape (t, sigma)
    fin_cases t
    · exact twoLevel_middle_cost z h z hz (orders (0, sigma)) hsh (positions 0)
    · exact twoLevel_middle_cost z h (j - h) (by omega) (orders (1, sigma)) hsh (positions 1)
    · exact twoLevel_bottom_cost z h (orders (2, sigma)) hsh (positions 2) hyh
  have hgap : ∀ v : Fin 3 × G,
      maximumGap (fun a => ((insertReferenceOrder (pos v) (orders v)).symm a).val)
        (extendZeroWeight (twoLevelHeight z)) = ![(2 : ℝ), 1, 1] v.1 := by
    intro v
    rcases v with ⟨t, sigma⟩
    have hsh := classProfile_block_shape z h starts baseOrders hshape (t, sigma)
    fin_cases t
    · exact twoLevel_top_gap z h z hh le_rfl (orders (0, sigma)) hsh (positions 0) hx
    · exact twoLevel_middle_gap z h (j - h) hh (by omega) (by omega) (orders (1, sigma)) hsh
        (positions 1) (by dsimp [positions]; omega)
    · exact twoLevel_bottom_gap z h (orders (2, sigma)) hsh (positions 2) hyh hym
  apply one_reference_equal_voter_realization g hg e a b c hab hbc hstrength orders pos
    (typeProfileWeight w) (typeProfileWeight_nonneg w hw) (typeProfileWeight_total w hwsum) hs hrefAvg
    (extendZeroWeight (twoLevelHeight z)) (extendZeroWeight_nonneg _ (twoLevelHeight_nonneg z)) (by simp)
    lam hlam
  change lam * expectation (typeProfileWeight (G := G) w) (fun v =>
      maximumGap (fun a => ((insertReferenceOrder (pos v) (orders v)).symm a).val)
        (extendZeroWeight (twoLevelHeight z))) <
    expectation (typeProfileWeight (G := G) w) (fun v =>
      expectation (extendZeroWeight (uniformVector m))
        (runningMin (fun a => ((insertReferenceOrder (pos v) (orders v)).symm a).val)
          (extendZeroWeight (twoLevelHeight z))))
  simp_rw [hgap, hcost]
  rw [typeProfile_constant_average, typeProfile_constant_average]
  exact hexcess

end OptimalG
