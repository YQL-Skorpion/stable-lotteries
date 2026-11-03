import OptimalG.BlockProfileWitness
import OptimalG.ProbabilityWeights

/-! # Five actual voter types realize the rounded Election 3 contradictions -/

namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

theorem expectation_sum_elim {T U : Type*} [Fintype T] [Fintype U]
    (w : T → ℝ) (v : U → ℝ) (f : T → ℝ) (g : U → ℝ) :
    expectation (Sum.elim w v) (Sum.elim f g) = expectation w f + expectation v g := by
  simp [expectation, Fintype.sum_sum_type]

/-- Three principal types plus a top/bottom auxiliary pair. The two auxiliary
weights can correct rounded class balance and create strict reference stability;
their loss of excess cost is bounded by 2λ times their total weight. -/
theorem three_class_auxiliary_grid_witness (g : ℝ → ℝ) (hg : Continuous g)
    (lam : ℝ) (hlam : 0 ≤ lam) (z h x y j r n : ℕ)
    (hz : 0 < z) (hh : 0 < h) (hx : x ≤ z) (hyh : h ≤ y) (hym : y < z + h)
    (hjh : h < j) (hjm : j ≤ z + h) (hrm : r ≤ z + h) [NeZero (z + h)]
    (e : PairedSupport n ≃ Fin (z + h)) (a b c : Fin (z + h))
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (hstrength : cyclicStrength g a (1 / (z + h : ℕ)) ≠ 0)
    (w : Fin 3 → ℝ) (hw : ∀ t, 0 ≤ w t) (hwsum : ∑ t, w t = 1)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hbalance : expectation w ![centeredPrimitive g ((z : ℝ) / (z + h : ℕ)),
      centeredPrimitive g (((j - h : ℕ) : ℝ) / (z + h : ℕ)) - centeredPrimitive g ((j : ℝ) / (z + h : ℕ)),
      -centeredPrimitive g ((h : ℝ) / (z + h : ℕ))] +
      u * centeredPrimitive g ((z : ℝ) / (z + h : ℕ)) - v * centeredPrimitive g ((h : ℝ) / (z + h : ℕ)) = 0)
    (hreference : expectation w (fun t =>
      ![g ((x : ℝ) / (z + h : ℕ)), g ((j : ℝ) / (z + h : ℕ)), g ((y : ℝ) / (z + h : ℕ))] t - activationPrimitive g 1) +
      (u + v) * (g ((r : ℝ) / (z + h : ℕ)) - activationPrimitive g 1) < 0)
    (hexcess : 0 < expectation w (fun t =>
      ![(x : ℝ) / (z + h : ℕ), (j : ℝ) / (z + h : ℕ), ((h : ℝ) + y) / (z + h : ℕ)] t - lam * ![2, 1, 1] t) -
      2 * lam * (u + v)) :
    WitnessAbove g (1 + 2 * lam) := by
  classical
  let m := z + h
  let T := Fin 3 ⊕ Fin 2
  let starts : T → ℕ := Sum.elim ![z, j - h, 0] ![z, 0]
  let pos : T → Fin (m + 1) := Sum.elim
    ![⟨x, by dsimp [m]; omega⟩, ⟨j, by dsimp [m]; omega⟩, ⟨y, by dsimp [m]; omega⟩]
    ![⟨r, by dsimp [m]; omega⟩, ⟨r, by dsimp [m]; omega⟩]
  let W : T → ℝ := Sum.elim w ![u, v]
  let N : T → ℝ := Sum.elim ![(x : ℝ) / m, (j : ℝ) / m, ((h : ℝ) + y) / m] ![0, 0]
  let G : T → ℝ := Sum.elim ![2, 1, 1] ![2, 2]
  have hW : ∀ t, 0 ≤ W t := by
    intro t
    rcases t with t | t
    · exact hw t
    · fin_cases t <;> assumption
  have hWsum : ∑ t, W t = 1 + u + v := by
    change (∑ t : Fin 3 ⊕ Fin 2, Sum.elim w ![u, v] t) = _
    simp [Fintype.sum_sum_type, Fin.sum_univ_two, hwsum]
    ring
  have hWpos : 0 < ∑ t, W t := by rw [hWsum]; linarith
  have hm : (m : ℝ) ≠ 0 := by dsimp [m]; positivity
  have hstarts : ∀ t, starts t ≤ z := by
    intro t
    rcases t with t | t <;> fin_cases t <;> dsimp [starts] <;> omega
  have hcenter : (fun t : T => centeredPrimitive g ((starts t : ℝ) / m) -
      centeredPrimitive g (((starts t + h : ℕ) : ℝ) / m)) = Sum.elim
        ![centeredPrimitive g ((z : ℝ) / m),
          centeredPrimitive g (((j - h : ℕ) : ℝ) / m) - centeredPrimitive g ((j : ℝ) / m),
          -centeredPrimitive g ((h : ℝ) / m)]
        ![centeredPrimitive g ((z : ℝ) / m), -centeredPrimitive g ((h : ℝ) / m)] := by
    funext t
    rcases t with t | t
    · fin_cases t
      · dsimp [starts]
        rw [show ((z + h : ℕ) : ℝ) / m = 1 from div_self hm]
        simp [centeredPrimitive]
      · dsimp [starts]
        rw [Nat.sub_add_cancel hjh.le]
      · dsimp [starts]
        simp [centeredPrimitive, activationPrimitive]
    · fin_cases t
      · dsimp [starts]
        rw [show ((z + h : ℕ) : ℝ) / m = 1 from div_self hm]
        simp [centeredPrimitive]
      · dsimp [starts]
        simp [centeredPrimitive, activationPrimitive]
  have hbalW : expectation W (fun t => centeredPrimitive g ((starts t : ℝ) / m) -
      centeredPrimitive g (((starts t + h : ℕ) : ℝ) / m)) = 0 := by
    rw [hcenter, expectation_sum_elim]
    change expectation w _ + expectation ![u, v] _ = 0
    simp only [expectation, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at *
    nlinarith only [hbalance]
  have hrefW : expectation W (fun t => g (((pos t).val : ℝ) / m) - activationPrimitive g 1) < 0 := by
    have he : (fun t : T => g (((pos t).val : ℝ) / m) - activationPrimitive g 1) = Sum.elim
        (fun t => ![g ((x : ℝ) / m), g ((j : ℝ) / m), g ((y : ℝ) / m)] t - activationPrimitive g 1)
        (fun _ : Fin 2 => g ((r : ℝ) / m) - activationPrimitive g 1) := by
      funext t
      rcases t with t | t <;> fin_cases t <;> rfl
    rw [he, expectation_sum_elim]
    have haux : expectation ![u, v] (fun _ : Fin 2 => g ((r : ℝ) / m) - activationPrimitive g 1) =
        (u + v) * (g ((r : ℝ) / m) - activationPrimitive g 1) := by simp [expectation, Fin.sum_univ_two]; ring
    rw [haux]
    exact hreference
  have hexcW : 0 < expectation W (fun t => N t - lam * G t) := by
    have he : (fun t : T => N t - lam * G t) = Sum.elim
        (fun t => ![(x : ℝ) / m, (j : ℝ) / m, ((h : ℝ) + y) / m] t - lam * ![2, 1, 1] t)
        (fun _ : Fin 2 => -(2 * lam)) := by
      funext t
      rcases t with t | t
      · rfl
      · fin_cases t <;> dsimp [N, G] <;> ring
    rw [he, expectation_sum_elim]
    have haux : expectation ![u, v] (fun _ : Fin 2 => -(2 * lam)) = -(2 * lam * (u + v)) := by
      simp [expectation, Fin.sum_univ_two]; ring
    rw [haux]
    exact hexcess
  apply block_profile_strict_witness g hg lam hlam z h n hz hh e a b c hab hbc hstrength starts hstarts pos
    (probabilityNormalize W) (probabilityNormalize_nonneg W hW) (probabilityNormalize_total W hWpos)
    (probabilityNormalize_zero W _ hbalW) (probabilityNormalize_reference W _ hWpos _ hrefW) N G
  · intro t order hs
    rcases t with t | t
    · fin_cases t
      · exact (twoLevel_middle_cost z h z hz order hs (pos (Sum.inl 0))).ge
      · exact (twoLevel_middle_cost z h (j - h) (by omega) order hs (pos (Sum.inl 1))).ge
      · exact (twoLevel_bottom_cost z h order hs (pos (Sum.inl 2)) hyh).ge
    · fin_cases t <;> exact twoLevel_cost_nonneg z h order _
  · intro t order hs
    rcases t with t | t
    · fin_cases t
      · exact (twoLevel_top_gap z h z hh le_rfl order hs (pos (Sum.inl 0)) hx).le
      · exact (twoLevel_middle_gap z h (j - h) hh (by omega) (by omega) order hs
          (pos (Sum.inl 1)) (by dsimp [pos]; omega)).le
      · exact (twoLevel_bottom_gap z h order hs (pos (Sum.inl 2)) hyh hym).le
    · fin_cases t <;> exact twoLevel_gap_le_two z h order _
  · exact probabilityNormalize_excess W N G hWpos lam hexcW

end OptimalG
