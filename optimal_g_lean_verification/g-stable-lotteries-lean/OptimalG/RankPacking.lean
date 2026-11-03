import OptimalG.Occupation
import OptimalG.ThresholdGeometry

/-! The packing inequalities (5.8), for actual finite candidate intervals. -/

namespace OptimalG

open Set MeasureTheory
open scoped BigOperators Interval

section

variable {n : ℕ} [Nonempty (Fin n)]

theorem occupation_prefix_one (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (S : Finset (Fin n)) (x : ℝ)
    (hx0 : 0 < x) (hxq : x ≤ rankCut D (prefixBoundary S)) :
    occupation D S x = 1 := by
  classical
  have hx1 : x ≤ 1 := le_trans hxq (rankCut_mem_Icc D hD hDsum _).2
  calc
    occupation D S x = occupation D Finset.univ x := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hcut := rankCut_mono D hD (prefixBoundary_le_outside S i hi)
      have hxi : x ≤ rankCut D i.val := le_trans hxq hcut
      simp [intervalOccupation, Set.indicator, Set.mem_Ioc, not_lt.mpr hxi]
    _ = intervalOccupation 0 1 x := occupation_univ D hD hDsum x
    _ = 1 := by simp [intervalOccupation, hx0, hx1]

omit [Nonempty (Fin n)] in
theorem occupation_zero_above_last (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i)
    (S : Finset (Fin n)) (x : ℝ) (hx : rankCut D (lastIndex S) < x) :
    occupation D S x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  have hindex := member_lt_lastIndex S i hi
  have hcut := rankCut_mono D hD (show i.val + 1 ≤ lastIndex S from hindex)
  have hxi : rankCut D (i.val + 1) < x := lt_of_le_of_lt hcut hx
  simp [intervalOccupation, Set.indicator, Set.mem_Ioc, not_le.mpr hxi]

theorem occupation_middle_mass (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (S : Finset (Fin n)) (q z : ℝ)
    (hq : q = rankCut D (prefixBoundary S))
    (hz : rankCut D (lastIndex S) ≤ z) (hz1 : z ≤ 1) :
    (∫ x in q..z, occupation D S x) = (∑ i ∈ S, D i) - q := by
  have hq0 : 0 ≤ q := by rw [hq]; exact (rankCut_mem_Icc D hD hDsum _).1
  have hqp : q ≤ ∑ i ∈ S, D i := by rw [hq]; exact prefixCut_le_mass D hD S
  have hpz := le_trans (mass_le_lastCut D hD S) hz
  have hqz : q ≤ z := le_trans hqp hpz
  have hleft : (∫ x in (0 : ℝ)..q, occupation D S x) = q := by
    calc
      _ = ∫ _x in (0 : ℝ)..q, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hq0
        intro x hx
        exact occupation_prefix_one D hD hDsum S x hx.1 (hq ▸ hx.2.le)
      _ = q := by simp
  have hright : (∫ x in z..1, occupation D S x) = 0 := by
    calc
      _ = ∫ _x in z..(1 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hz1
        intro x hx
        exact occupation_zero_above_last D hD S x (lt_of_le_of_lt hz hx.1)
      _ = 0 := by simp
  have htotal := occupation_mass D hD hDsum S
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (occupation_integrable D S 0 q) (occupation_integrable D S q z)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (occupation_integrable D S 0 z) (occupation_integrable D S z 1)
  linarith

noncomputable def curvePrimitive (phi : ℝ → ℝ) (r : ℝ) : ℝ := ∫ x in (0 : ℝ)..r, phi x

noncomputable def centeredBlock (D : Fin n → ℝ) (S : Finset (Fin n)) (phi : ℝ → ℝ) : ℝ :=
  -(∑ i ∈ S, ∫ x in rankCut D i.val..rankCut D (i.val + 1), phi x)

/-- All centered activation of a candidate set is bounded by filling its remaining
mass against the right endpoint z, with its initial prefix fixed. -/
theorem centeredBlock_packing (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (S : Finset (Fin n)) (phi : ℝ → ℝ)
    (hcont : ContinuousOn phi (Icc 0 1)) (hanti : AntitoneOn phi (Icc 0 1))
    (p q z : ℝ) (hp : p = ∑ i ∈ S, D i)
    (hq : q = rankCut D (prefixBoundary S))
    (hz : rankCut D (lastIndex S) ≤ z) (hz1 : z ≤ 1) :
    centeredBlock D S phi ≤
      curvePrimitive phi (z - p + q) - curvePrimitive phi z - curvePrimitive phi q := by
  have hq0 : 0 ≤ q := by rw [hq]; exact (rankCut_mem_Icc D hD hDsum _).1
  have hqp : q ≤ p := by rw [hq, hp]; exact prefixCut_le_mass D hD S
  have hpz : p ≤ z := by rw [hp]; exact le_trans (mass_le_lastCut D hD S) hz
  have hqz : q ≤ z := le_trans hqp hpz
  have hz0 : 0 ≤ z := le_trans hq0 hqz
  have hcq : q ≤ z - p + q := by linarith
  have hcz : z - p + q ≤ z := by linarith
  have hc0 : 0 ≤ z - p + q := le_trans hq0 hcq
  have hphi : IntervalIntegrable phi volume 0 1 := hcont.intervalIntegrable_of_Icc (by norm_num)
  have hint (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :=
    intervalIntegrable_on_subinterval hphi (by norm_num) ha hab hb
  have hoccint (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
      IntervalIntegrable (fun x => occupation D S x * phi x) volume a b := by
    apply (occupation_integrable D S a b).mul_continuousOn
    rw [uIcc_of_le hab]
    exact hcont.mono (Icc_subset_Icc ha hb)
  have hpack := pack_right_antitone phi (occupation D S) q (z - p + q) z hcq hcz
    (hcont.mono (Icc_subset_Icc hq0 hz1))
    (hanti.mono (Icc_subset_Icc hq0 hz1)) (occupation_integrable D S q z)
    (fun x _ => ⟨occupation_nonneg D S x, occupation_le_one D hD hDsum S x⟩)
    (by rw [occupation_middle_mass D hD hDsum S q z hq hz hz1, ← hp]; ring)
  have hleft : (∫ x in (0 : ℝ)..q, occupation D S x * phi x) = curvePrimitive phi q := by
    apply intervalIntegral.integral_congr_Ioo_of_le hq0
    intro x hx
    change occupation D S x * phi x = phi x
    rw [occupation_prefix_one D hD hDsum S x hx.1 (hq ▸ hx.2.le), one_mul]
  have hright : (∫ x in z..1, occupation D S x * phi x) = 0 := by
    calc
      _ = ∫ _x in z..(1 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hz1
        intro x hx
        change occupation D S x * phi x = 0
        rw [occupation_zero_above_last D hD S x (lt_of_le_of_lt hz hx.1), zero_mul]
      _ = 0 := by simp
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (hoccint 0 q le_rfl hq0 (le_trans hqz hz1)) (hoccint q z hq0 hqz hz1)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (hoccint 0 z le_rfl hz0 hz1) (hoccint z 1 hz0 hz1 le_rfl)
  have htop := intervalIntegral.integral_add_adjacent_intervals
    (hint 0 (z - p + q) le_rfl hc0 (le_trans hcz hz1))
    (hint (z - p + q) z hc0 hcz hz1)
  have hblock := occupation_weighted_integral D hD hDsum S phi hcont
  unfold centeredBlock curvePrimitive at *
  linarith

end
end OptimalG
