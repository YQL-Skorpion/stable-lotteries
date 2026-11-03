import OptimalG.BlockGeometry

/-! # Actual finite rankings with a contiguous zero-height class -/

namespace OptimalG
open scoped BigOperators

def rankBlock (m k l : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => k ≤ i.val ∧ i.val < l)

@[simp] theorem mem_rankBlock (m k l : ℕ) (i : Fin m) :
    i ∈ rankBlock m k l ↔ k ≤ i.val ∧ i.val < l := by simp [rankBlock]

theorem card_rankBlock (m k l : ℕ) (hkl : k ≤ l) (hlm : l ≤ m) :
    (rankBlock m k l).card = l - k := by
  symm
  calc
    l - k = (Finset.univ : Finset (Fin (l - k))).card := by simp
    _ = _ := by
      apply Finset.card_bij (fun (i : Fin (l - k)) _ => (⟨k + i.val, by omega⟩ : Fin m))
      · intro i _
        simp only [mem_rankBlock]
        have := i.isLt
        omega
      · intro i _ j _ hij
        apply Fin.ext
        have := congrArg Fin.val hij
        simpa using this
      · intro j hj
        simp only [mem_rankBlock] at hj
        refine ⟨⟨j.val - k, by omega⟩, Finset.mem_univ _, ?_⟩
        apply Fin.ext
        dsimp
        omega

def binaryHeight {m : ℕ} (h : ℕ) (i : Fin m) : ℝ := if i.val < h then 1 else 0

theorem binaryHeight_nonneg {m : ℕ} (h : ℕ) (i : Fin m) : 0 ≤ binaryHeight h i := by
  unfold binaryHeight; split_ifs <;> norm_num

theorem binaryHeight_le_one {m : ℕ} (h : ℕ) (i : Fin m) : binaryHeight h i ≤ 1 := by
  unfold binaryHeight; split_ifs <;> norm_num

/-- For any split k of the high class, an actual permutation places the zero
class in the middle block [k,k+z), where z is its cardinality. -/
theorem exists_binary_block_order (h z k : ℕ) (hk : k ≤ h) :
    ∃ order : Equiv.Perm (Fin (h + z)), ∀ i,
      binaryHeight h (order i) = if i.val < k ∨ k + z ≤ i.val then 1 else 0 := by
  have hc : (rankBlock (h + z) k (k + z)).card =
      (rankBlock (h + z) h (h + z)).card := by
    rw [card_rankBlock _ _ _ (by omega) (by omega),
      card_rankBlock _ _ _ (by omega) (by omega)]
    omega
  obtain ⟨order, hmap⟩ := Equiv.Perm.exists_map_finset_eq
    (rankBlock (h + z) k (k + z)) (rankBlock (h + z) h (h + z)) hc
  refine ⟨order, fun i => ?_⟩
  have hiff : h ≤ (order i).val ↔ k ≤ i.val ∧ i.val < k + z := by
    have hm : order i ∈ (rankBlock (h + z) k (k + z)).map order.toEmbedding ↔
        order i ∈ rankBlock (h + z) h (h + z) := by rw [hmap]
    simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_rankBlock,
      (order i).isLt, and_true] using hm.symm
  unfold binaryHeight
  split_ifs with hhigh houtside
  · rfl
  · exfalso
    have hi : k ≤ i.val ∧ i.val < k + z := by omega
    have := hiff.mpr hi
    omega
  · exfalso
    have hi := hiff.mp (Nat.le_of_not_gt hhigh)
    omega
  · rfl

theorem binary_block_geometry (h z k : ℕ) (hz : 0 < z) (hk : k ≤ h)
    [NeZero (h + z)] (order : Equiv.Perm (Fin (h + z)))
    (hshape : ∀ i, binaryHeight h (order i) = if i.val < k ∨ k + z ≤ i.val then 1 else 0) :
    expectation (uniformVector (h + z))
      (runningMin (fun x => (order.symm x).val) (binaryHeight h)) = (k : ℝ) / (h + z : ℕ) ∧
      maximumGap (fun x => (order.symm x).val) (binaryHeight h) = if k < h then 1 else 0 := by
  let q : Fin (h + z) := ⟨k, by omega⟩
  have hbefore : ∀ i : Fin (h + z), i.val < q.val → binaryHeight h (order i) = 1 := by
    intro i hi
    rw [hshape, if_pos (Or.inl hi)]
  have hzero : binaryHeight h (order q) = 0 := by
    rw [hshape, if_neg]
    dsimp [q]
    omega
  constructor
  · exact first_zero_uniform_cost order (binaryHeight h) q (binaryHeight_nonneg h) hbefore hzero
  · by_cases hkh : k < h
    · rw [if_pos hkh]
      let j : Fin (h + z) := ⟨k + z, by omega⟩
      apply first_zero_gap_eq_one order (binaryHeight h) q (binaryHeight_nonneg h)
        (binaryHeight_le_one h) hbefore hzero j (by dsimp [q, j]; omega)
      rw [hshape, if_pos (Or.inr le_rfl)]
    · rw [if_neg hkh]
      apply first_zero_gap_eq_zero order (binaryHeight h) q (binaryHeight_nonneg h) hbefore
      intro i hi
      rw [hshape, if_neg]
      dsimp [q] at hi
      have := i.isLt
      omega

end OptimalG
