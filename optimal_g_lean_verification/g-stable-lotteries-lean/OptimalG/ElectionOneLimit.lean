import OptimalG.ElectionOne
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Passing Election 1 from finite grids to real two-point tests

Candidate ranks and voter proportions are both approximated by lower grid
points with denominator n+1. The endpoint 1 is preserved exactly, so the jump
in the excess-cost function at rank 1 causes no loss in the limit.
-/

namespace OptimalG

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable def lowerGrid (n : ℕ) (r : ℝ) : ℝ :=
  (⌊((n + 1 : ℕ) : ℝ) * r⌋₊ : ℝ) / (n + 1 : ℕ)

noncomputable def lowerGridIndex (n : ℕ) (r : ℝ) (hr : r ∈ Icc 0 1) : Fin ((n + 1) + 1) :=
  ⟨⌊((n + 1 : ℕ) : ℝ) * r⌋₊,
    Nat.lt_succ_of_le (Nat.floor_le_of_le (mul_le_of_le_one_right (Nat.cast_nonneg _) hr.2))⟩

theorem lowerGrid_nonneg (n : ℕ) (r : ℝ) : 0 ≤ lowerGrid n r := by
  unfold lowerGrid
  positivity

theorem lowerGrid_le (n : ℕ) (r : ℝ) (hr : 0 ≤ r) : lowerGrid n r ≤ r := by
  have hden : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  apply (div_le_iff₀ hden).mpr
  have h := Nat.floor_le (mul_nonneg (Nat.cast_nonneg (n + 1)) hr)
  simpa only [mul_comm] using h

theorem lowerGrid_error (n : ℕ) (r : ℝ) : r - 1 / ((n + 1 : ℕ) : ℝ) < lowerGrid n r := by
  have hden : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  apply (lt_div_iff₀ hden).mpr
  have h := Nat.lt_floor_add_one (((n + 1 : ℕ) : ℝ) * r)
  have hdiv : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) * (n + 1 : ℕ) = 1 :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  nlinarith

theorem lowerGrid_mem_Icc (n : ℕ) (r : ℝ) (hr : r ∈ Icc 0 1) :
    lowerGrid n r ∈ Icc 0 1 :=
  ⟨lowerGrid_nonneg n r, le_trans (lowerGrid_le n r hr.1) hr.2⟩

theorem lowerGrid_tendsto (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun n => lowerGrid n r) atTop (𝓝 r) := by
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1 : ℕ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using tendsto_const_nhds.sub hinv) tendsto_const_nhds
  · intro n
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using le_of_lt (lowerGrid_error n r)
  · intro n
    exact lowerGrid_le n r hr

theorem lowerGridIndex_last_iff (n : ℕ) (r : ℝ) (hr : r ∈ Icc 0 1) :
    lowerGridIndex n r hr = Fin.last (n + 1) ↔ r = 1 := by
  constructor
  · intro h
    have hval : ⌊((n + 1 : ℕ) : ℝ) * r⌋₊ = n + 1 := congrArg Fin.val h
    have hfloor := Nat.floor_le (mul_nonneg (Nat.cast_nonneg (n + 1)) hr.1)
    rw [hval] at hfloor
    have hden : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    apply le_antisymm hr.2
    nlinarith
  · intro h
    subst r
    apply Fin.ext
    change ⌊((n + 1 : ℕ) : ℝ) * 1⌋₊ = n + 1
    rw [mul_one, Nat.floor_natCast]

theorem continuous_lowerGrid_tendsto (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 1)) (r : ℝ) (hr : r ∈ Icc 0 1) :
    Tendsto (fun n => g (lowerGrid n r)) atTop (𝓝 (g r)) := by
  apply (hg r hr).tendsto.comp
  exact tendsto_nhdsWithin_iff.mpr
    ⟨lowerGrid_tendsto r hr.1, Eventually.of_forall (fun n => lowerGrid_mem_Icc n r hr)⟩

/-- Exact uniform average of a finite two-valued voter list. -/
theorem binary_uniform_average (N k : ℕ) (hN : 0 < N) (hk : k ≤ N) (A B : ℝ) :
    (∑ i : Fin N, if i.val < k then A else B) / N =
      (k : ℝ) / N * A + (1 - (k : ℝ) / N) * B := by
  have hpoint : ∀ i : ℕ, (if i < k then A else B) = (if i < k then A - B else 0) + B := by
    intro i
    split_ifs <;> ring
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < k then A else B) N]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_filter]
  have hfilter : (Finset.range N).filter (fun i => i < k) = Finset.range k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  field_simp
  ring

noncomputable def binaryGridRanks (n : ℕ)
    (theta r s : ℝ) (htheta : theta ∈ Icc 0 1) (hr : r ∈ Icc 0 1) (hs : s ∈ Icc 0 1)
    (i : Fin (n + 1)) : Fin ((n + 1) + 1) :=
  if i.val < (lowerGridIndex n theta htheta).val then lowerGridIndex n r hr else lowerGridIndex n s hs

theorem binaryGrid_average (n : ℕ) (theta r s : ℝ)
    (htheta : theta ∈ Icc 0 1) (hr : r ∈ Icc 0 1) (hs : s ∈ Icc 0 1)
    (f : Fin ((n + 1) + 1) → ℝ) :
    (∑ i : Fin (n + 1), f (binaryGridRanks n theta r s htheta hr hs i)) / (n + 1 : ℕ) =
      lowerGrid n theta * f (lowerGridIndex n r hr) +
        (1 - lowerGrid n theta) * f (lowerGridIndex n s hs) := by
  simp only [binaryGridRanks, apply_ite]
  exact binary_uniform_average (n + 1) (lowerGridIndex n theta htheta).val (Nat.succ_pos _)
    (Nat.le_of_lt_succ (lowerGridIndex n theta htheta).isLt) _ _

/-- The discontinuous denominator contribution from Election 1. -/
noncomputable def rankOneGap (r : ℝ) : ℝ := if r = 1 then 0 else 1

/-- Every strict real two-point test is realized by an actual finite election. -/
theorem real_twoPoint_strict_witness (g : ℝ → ℝ) (lam theta r s : ℝ)
    (hlam : 0 ≤ lam) (hg : ContinuousOn g (Icc 0 1))
    (htheta : theta ∈ Icc 0 1) (hr : r ∈ Icc 0 1) (hs : s ∈ Icc 0 1)
    (hactivation : theta * g r + (1 - theta) * g s < ∫ x in (0 : ℝ)..1, g x)
    (hexcess : lam * (theta * rankOneGap r + (1 - theta) * rankOneGap s) <
      theta * r + (1 - theta) * s) : WitnessAbove g (1 + 2 * lam) := by
  let act := fun n => lowerGrid n theta * g (lowerGrid n r) +
    (1 - lowerGrid n theta) * g (lowerGrid n s)
  let excess := fun n => lowerGrid n theta * lowerGrid n r +
    (1 - lowerGrid n theta) * lowerGrid n s -
      lam * (lowerGrid n theta * rankOneGap r + (1 - lowerGrid n theta) * rankOneGap s)
  have ht := lowerGrid_tendsto theta htheta.1
  have hrt := lowerGrid_tendsto r hr.1
  have hst := lowerGrid_tendsto s hs.1
  have hact : Tendsto act atTop (𝓝 (theta * g r + (1 - theta) * g s)) :=
    (ht.mul (continuous_lowerGrid_tendsto g hg r hr)).add
      ((tendsto_const_nhds.sub ht).mul (continuous_lowerGrid_tendsto g hg s hs))
  have hex : Tendsto excess atTop (𝓝 (theta * r + (1 - theta) * s -
      lam * (theta * rankOneGap r + (1 - theta) * rankOneGap s))) :=
    ((ht.mul hrt).add ((tendsto_const_nhds.sub ht).mul hst)).sub
      (tendsto_const_nhds.mul ((ht.mul tendsto_const_nhds).add
        ((tendsto_const_nhds.sub ht).mul tendsto_const_nhds)))
  have hevent := (hact.eventually_lt_const hactivation).and
    (hex.eventually_const_lt (sub_pos.mpr hexcess))
  obtain ⟨n, han, hen⟩ := hevent.exists
  apply electionOneFinite_witnessAbove (n + 1) (Nat.succ_pos n)
    (binaryGridRanks n theta r s htheta hr hs) g lam hlam hg
  · rw [Fintype.card_fin]
    have havg := binaryGrid_average n theta r s htheta hr hs
      (fun k => g ((k.val : ℝ) / (n + 1 : ℕ)))
    rw [havg]
    exact le_of_lt han
  · rw [Fintype.card_fin]
    have hden := binaryGrid_average n theta r s htheta hr hs
      (fun k => if k = Fin.last (n + 1) then (0 : ℝ) else 1)
    have hnum := binaryGrid_average n theta r s htheta hr hs
      (fun k => (k.val : ℝ) / (n + 1 : ℕ))
    rw [hden, hnum]
    simp only [lowerGridIndex_last_iff]
    change lam * (lowerGrid n theta * rankOneGap r + (1 - lowerGrid n theta) * rankOneGap s) <
      lowerGrid n theta * lowerGrid n r + (1 - lowerGrid n theta) * lowerGrid n s
    exact sub_pos.mp hen

/-- A weak activation inequality can be made strict by mixing infinitesimally
more of a rank whose activation is strictly below the mean. -/
theorem real_twoPoint_weak_witness (g : ℝ → ℝ) (lam theta r s : ℝ)
    (hlam : 0 ≤ lam) (hg : ContinuousOn g (Icc 0 1))
    (htheta : theta ∈ Icc 0 1) (hr : r ∈ Icc 0 1) (hs : s ∈ Icc 0 1)
    (hsbelow : g s < ∫ x in (0 : ℝ)..1, g x)
    (hactivation : theta * g r + (1 - theta) * g s ≤ ∫ x in (0 : ℝ)..1, g x)
    (hexcess : lam * (theta * rankOneGap r + (1 - theta) * rankOneGap s) <
      theta * r + (1 - theta) * s) : WitnessAbove g (1 + 2 * lam) := by
  let eps := fun n : ℕ => (1 : ℝ) / (n + 1 : ℕ)
  let weight := fun n => (1 - eps n) * theta
  have heps : Tendsto eps atTop (𝓝 0) := by
    simpa only [eps, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hweight : Tendsto weight atTop (𝓝 theta) := by
    simpa [weight] using ((tendsto_const_nhds (x := (1 : ℝ))).sub heps).mul_const theta
  have hlimit : Tendsto (fun n => weight n * r + (1 - weight n) * s -
      lam * (weight n * rankOneGap r + (1 - weight n) * rankOneGap s))
      atTop (𝓝 (theta * r + (1 - theta) * s -
        lam * (theta * rankOneGap r + (1 - theta) * rankOneGap s))) :=
    ((hweight.mul_const r).add ((tendsto_const_nhds.sub hweight).mul_const s)).sub
      (tendsto_const_nhds.mul ((hweight.mul_const (rankOneGap r)).add
        ((tendsto_const_nhds.sub hweight).mul_const (rankOneGap s))))
  obtain ⟨n, hn⟩ := (hlimit.eventually_const_lt (sub_pos.mpr hexcess)).exists
  have hepsPos : 0 < eps n := by dsimp [eps]; positivity
  have hepsLe : eps n ≤ 1 := by
    dsimp [eps]
    apply (div_le_one (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
    exact_mod_cast Nat.succ_pos n
  have hnonneg : 0 ≤ 1 - eps n := sub_nonneg.mpr hepsLe
  have hw0 : 0 ≤ weight n := mul_nonneg hnonneg htheta.1
  have hw1 : weight n ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left htheta.2 hnonneg
    dsimp [weight]
    nlinarith
  apply real_twoPoint_strict_witness g lam (weight n) r s hlam hg ⟨hw0, hw1⟩ hr hs
  · have h1 := mul_le_mul_of_nonneg_left hactivation hnonneg
    have h2 := mul_lt_mul_of_pos_left hsbelow hepsPos
    dsimp [weight]
    nlinarith
  · exact sub_pos.mp hn

/-- The weak two-rank necessary condition used for scalar separation in A.2. -/
theorem real_twoPoint_necessary (g : ℝ → ℝ) (lam theta r s : ℝ)
    (hlam : 0 ≤ lam) (hg : ContinuousOn g (Icc 0 1))
    (hbound : UniversalBound g (1 + 2 * lam))
    (htheta : theta ∈ Icc 0 1) (hr : r ∈ Icc 0 1) (hs : s ∈ Icc 0 1)
    (hsbelow : g s < ∫ x in (0 : ℝ)..1, g x)
    (hactivation : theta * g r + (1 - theta) * g s ≤ ∫ x in (0 : ℝ)..1, g x) :
    theta * r + (1 - theta) * s ≤
      lam * (theta * rankOneGap r + (1 - theta) * rankOneGap s) := by
  by_contra h
  exact witnessAbove_not_universalBound g _
    (real_twoPoint_weak_witness g lam theta r s hlam hg htheta hr hs hsbelow hactivation
      (lt_of_not_ge h)) hbound

end OptimalG
