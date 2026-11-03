import OptimalG.TwoLevelBlocks

/-! # Exact maximum gaps for the three Election 3 voter types -/

namespace OptimalG

theorem twoLevel_gap_le_two (z h : ℕ) [NeZero (z + h)]
    (order : Equiv.Perm (Fin (z + h))) (k : Fin (z + h + 1)) :
    maximumGap (fun a => ((insertReferenceOrder k order).symm a).val)
      (extendZeroWeight (twoLevelHeight z)) ≤ 2 := by
  apply insertReference_gap_le k order _ (twoLevelHeight_nonneg z) 2 (by norm_num)
  intro i
  have hu := (twoLevelHeight_bounds z (order i)).2
  have hn := runningMin_nonneg (fun a => (order.symm a).val) (twoLevelHeight z) (twoLevelHeight_nonneg z) (order i)
  split_ifs <;> linarith

theorem twoLevel_top_gap (z h l : ℕ) [NeZero (z + h)] (hh : 0 < h) (hlz : l ≤ z)
    (order : Equiv.Perm (Fin (z + h)))
    (hshape : ∀ i, binaryHeight z (order i) = if i.val < l ∨ l + h ≤ i.val then 1 else 0)
    (k : Fin (z + h + 1)) (hkl : k.val ≤ l) :
    maximumGap (fun a => ((insertReferenceOrder k order).symm a).val)
      (extendZeroWeight (twoLevelHeight z)) = 2 := by
  apply le_antisymm (twoLevel_gap_le_two z h order k)
  let j : Fin (z + h) := ⟨l, by omega⟩
  have he := le_maximumGap (fun a => ((insertReferenceOrder k order).symm a).val)
    (extendZeroWeight (twoLevelHeight z)) (order j).castSucc
  rw [extendZeroWeight_castSucc, runningMin_insertReference k order _ (twoLevelHeight_nonneg z),
    if_neg (by dsimp [j]; omega), sub_zero, twoLevel_block_shape z h l order hshape] at he
  simpa only [j, if_pos (show l ≤ l ∧ l < l + h by omega)] using he

theorem twoLevel_middle_gap (z h l : ℕ) [NeZero (z + h)]
    (hh : 0 < h) (hl : 0 < l) (hlz : l ≤ z)
    (order : Equiv.Perm (Fin (z + h)))
    (hshape : ∀ i, binaryHeight z (order i) = if i.val < l ∨ l + h ≤ i.val then 1 else 0)
    (k : Fin (z + h + 1)) (hk : l + h ≤ k.val) :
    maximumGap (fun a => ((insertReferenceOrder k order).symm a).val)
      (extendZeroWeight (twoLevelHeight z)) = 1 := by
  apply le_antisymm
  · apply insertReference_gap_le k order _ (twoLevelHeight_nonneg z) 1 (by norm_num)
    intro i
    rw [twoLevel_middle_minimum z h l hl order hshape]
    by_cases hi : i.val < k.val
    · rw [if_pos hi]
      linarith [(twoLevelHeight_bounds z (order i)).2]
    · rw [if_neg hi, twoLevel_block_shape z h l order hshape, if_neg (by omega)]
      norm_num
  · let j : Fin (z + h) := ⟨l, by omega⟩
    have he := le_maximumGap (fun a => ((insertReferenceOrder k order).symm a).val)
      (extendZeroWeight (twoLevelHeight z)) (order j).castSucc
    rw [extendZeroWeight_castSucc, runningMin_insertReference k order _ (twoLevelHeight_nonneg z),
      if_pos (by dsimp [j]; omega), twoLevel_middle_minimum z h l hl order hshape,
      twoLevel_block_shape z h l order hshape] at he
    simpa only [j, if_pos (show l ≤ l ∧ l < l + h by omega), show (2 : ℝ) - 1 = 1 by norm_num] using he

theorem twoLevel_bottom_gap (z h : ℕ) [NeZero (z + h)]
    (order : Equiv.Perm (Fin (z + h)))
    (hshape : ∀ i, binaryHeight z (order i) = if i.val < 0 ∨ 0 + h ≤ i.val then 1 else 0)
    (k : Fin (z + h + 1)) (hkh : h ≤ k.val) (hkm : k.val < z + h) :
    maximumGap (fun a => ((insertReferenceOrder k order).symm a).val)
      (extendZeroWeight (twoLevelHeight z)) = 1 := by
  have hheight (i : Fin (z + h)) : twoLevelHeight z (order i) = if i.val < h then 2 else 1 := by
    rw [twoLevel_block_shape z h 0 order hshape]
    simp
  apply le_antisymm
  · apply insertReference_gap_le k order _ (twoLevelHeight_nonneg z) 1 (by norm_num)
    intro i
    rw [twoLevel_bottom_minimum z h order hshape, hheight]
    split_ifs <;> first | omega | norm_num
  · let j : Fin (z + h) := ⟨k.val, hkm⟩
    have he := le_maximumGap (fun a => ((insertReferenceOrder k order).symm a).val)
      (extendZeroWeight (twoLevelHeight z)) (order j).castSucc
    rw [extendZeroWeight_castSucc, runningMin_insertReference k order _ (twoLevelHeight_nonneg z),
      if_neg (by dsimp [j]; omega), sub_zero, hheight, if_neg (by dsimp [j]; omega)] at he
    exact he

end OptimalG
