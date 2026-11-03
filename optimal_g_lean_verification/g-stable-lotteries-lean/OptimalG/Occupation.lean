import OptimalG.RankIntegral
import OptimalG.Packing

/-! Occupation functions of finite candidate blocks on the rank line. -/

namespace OptimalG

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable def intervalOccupation (a b x : ℝ) : ℝ :=
  (Ioc a b).indicator (fun _ => 1) x

theorem intervalOccupation_nonneg (a b x : ℝ) : 0 ≤ intervalOccupation a b x := by
  simp only [intervalOccupation, indicator]
  split_ifs <;> norm_num

theorem intervalOccupation_adjacent (a b c x : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    intervalOccupation a b x + intervalOccupation b c x = intervalOccupation a c x := by
  by_cases hax : a < x
  · by_cases hbx : b < x
    · have hxb : ¬ x ≤ b := not_le.mpr hbx
      simp [intervalOccupation, Set.indicator, Set.mem_Ioc, hax, hbx, hxb]
    · have hxb : x ≤ b := le_of_not_gt hbx
      have hxc : x ≤ c := le_trans hxb hbc
      simp [intervalOccupation, Set.indicator, Set.mem_Ioc, hax, hbx, hxb, hxc]
  · have hbx : ¬ b < x := not_lt.mpr (le_trans (le_of_not_gt hax) hab)
    simp [intervalOccupation, Set.indicator, Set.mem_Ioc, hax, hbx]

theorem sum_intervalOccupation (cuts : ℕ → ℝ) (hmono : Monotone cuts) (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range n, intervalOccupation (cuts k) (cuts (k + 1)) x) =
      intervalOccupation (cuts 0) (cuts n) x := by
  induction n with
  | zero => simp [intervalOccupation]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    exact intervalOccupation_adjacent _ _ _ _ (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n))

theorem intervalIntegrable_indicator {f : ℝ → ℝ} {a b : ℝ} {s : Set ℝ}
    (hf : IntervalIntegrable f volume a b) (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator f) volume a b :=
  ⟨hf.1.indicator hs, hf.2.indicator hs⟩

theorem intervalOccupation_integrable (a b L R : ℝ) :
    IntervalIntegrable (intervalOccupation a b) volume L R :=
  intervalIntegrable_indicator intervalIntegrable_const measurableSet_Ioc

/-- Restricting an integral to a contained interval recovers that interval's integral. -/
theorem integral_indicator_subinterval (f : ℝ → ℝ) (L a b R : ℝ)
    (hLa : L ≤ a) (hab : a ≤ b) (hbR : b ≤ R) :
    (∫ x in L..R, (Ioc a b).indicator f x) = ∫ x in a..b, f x := by
  have hLR : L ≤ R := le_trans hLa (le_trans hab hbR)
  rw [intervalIntegral.integral_of_le hLR, MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, intervalIntegral.integral_of_le hab]
  congr 1
  congr 1
  exact inter_eq_left.mpr (Ioc_subset_Ioc hLa hbR)

theorem integral_intervalOccupation (L a b R : ℝ)
    (hLa : L ≤ a) (hab : a ≤ b) (hbR : b ≤ R) :
    (∫ x in L..R, intervalOccupation a b x) = b - a := by
  change (∫ x in L..R, (Ioc a b).indicator (fun _ : ℝ => (1 : ℝ)) x) = b - a
  rw [integral_indicator_subinterval _ L a b R hLa hab hbR]
  simp

section FiniteRankLine

variable {n : ℕ}

noncomputable def occupation (D : Fin n → ℝ) (S : Finset (Fin n)) (x : ℝ) : ℝ :=
  ∑ i ∈ S, intervalOccupation (rankCut D i.val) (rankCut D (i.val + 1)) x

theorem occupation_nonneg (D : Fin n → ℝ) (S : Finset (Fin n)) (x : ℝ) :
    0 ≤ occupation D S x :=
  Finset.sum_nonneg (fun _i _ => intervalOccupation_nonneg _ _ _)

theorem occupation_mono_set (D : Fin n → ℝ) (S T : Finset (Fin n)) (hST : S ⊆ T) (x : ℝ) :
    occupation D S x ≤ occupation D T x := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hST
  intro i _ _
  exact intervalOccupation_nonneg _ _ _

theorem occupation_univ (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (x : ℝ) :
    occupation D Finset.univ x = intervalOccupation 0 1 x := by
  have h := sum_intervalOccupation (rankCut D) (rankCut_mono D hD) n x
  rw [Finset.sum_range] at h
  simpa only [occupation, rankCut_zero, rankCut_end D hDsum] using h

theorem occupation_le_one (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (S : Finset (Fin n)) (x : ℝ) :
    occupation D S x ≤ 1 := by
  calc
    occupation D S x ≤ occupation D Finset.univ x :=
      occupation_mono_set D S Finset.univ (Finset.subset_univ _) x
    _ = intervalOccupation 0 1 x := occupation_univ D hD hDsum x
    _ ≤ 1 := by simp only [intervalOccupation, indicator]; split_ifs <;> norm_num

theorem occupation_integrable (D : Fin n → ℝ) (S : Finset (Fin n)) (L R : ℝ) :
    IntervalIntegrable (occupation D S) volume L R := by
  have hf : occupation D S =
      ∑ i ∈ S, fun x => intervalOccupation (rankCut D i.val) (rankCut D (i.val + 1)) x := by
    funext x
    simp [occupation]
  rw [hf]
  exact IntervalIntegrable.sum S (fun i _ => intervalOccupation_integrable _ _ _ _)

theorem occupation_mass (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (S : Finset (Fin n)) :
    (∫ x in (0 : ℝ)..1, occupation D S x) = ∑ i ∈ S, D i := by
  unfold occupation
  rw [intervalIntegral.integral_finsetSum (fun i _ => intervalOccupation_integrable _ _ _ _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_intervalOccupation 0 _ _ 1 (rankCut_mem_Icc D hD hDsum i.val).1
    (rankCut_mono D hD (Nat.le_succ i.val)) (rankCut_mem_Icc D hD hDsum (i.val + 1)).2]
  rw [rankCut_succ]
  ring

theorem occupation_weighted_integral (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (S : Finset (Fin n)) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 1)) :
    (∫ x in (0 : ℝ)..1, occupation D S x * f x) =
      ∑ i ∈ S, ∫ x in rankCut D i.val..rankCut D (i.val + 1), f x := by
  have hfu : ContinuousOn f (uIcc 0 1) := by simpa using hf
  have heq : (fun x => occupation D S x * f x) = fun x =>
      ∑ i ∈ S, (Ioc (rankCut D i.val) (rankCut D (i.val + 1))).indicator f x := by
    funext x
    simp only [occupation, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [intervalOccupation, indicator]
    split_ifs <;> simp
  rw [heq, intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_indicator_subinterval f 0 _ _ 1 (rankCut_mem_Icc D hD hDsum i.val).1
      (rankCut_mono D hD (Nat.le_succ i.val)) (rankCut_mem_Icc D hD hDsum (i.val + 1)).2
  · intro i _
    exact intervalIntegrable_indicator (hf.intervalIntegrable_of_Icc (by norm_num)) measurableSet_Ioc

end FiniteRankLine

end OptimalG
