import OptimalG.ElectionOneLimit
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Election 1 forces the centered activation bound

This module derives the separating scale from actual finite-election witnesses.
The positive-ratio supremum is proved bounded using the real two-rank test,
which in turn was obtained by finite grid approximation. No separation theorem,
finite-election realizability claim, or bound on the activation is assumed.
-/

namespace OptimalG

open Set MeasureTheory
open scoped BigOperators

/-- The discontinuous excess-cost function of Election 1. -/
noncomputable def rankOneExcess (lam r : ℝ) : ℝ := r - lam * rankOneGap r

@[simp] theorem rankOneExcess_one (lam : ℝ) : rankOneExcess lam 1 = 1 := by
  simp [rankOneExcess, rankOneGap]

/-- A continuous function with its endpoint above its mean must be below its
mean somewhere else. -/
theorem exists_rank_below_mean (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 1))
    (hendpoint : (∫ r in (0 : ℝ)..1, g r) < g 1) :
    ∃ s ∈ Icc (0 : ℝ) 1, g s < ∫ r in (0 : ℝ)..1, g r := by
  let mean := ∫ r in (0 : ℝ)..1, g r
  by_contra! hnone
  have hcont : ContinuousOn (fun r => g r - mean) (Icc 0 1) := hg.sub continuousOn_const
  have hpos := intervalIntegral.integral_pos (show (0 : ℝ) < 1 by norm_num) hcont
    (fun r hr => sub_nonneg.mpr (hnone r ⟨le_of_lt hr.1, hr.2⟩))
    ⟨1, by norm_num, sub_pos.mpr hendpoint⟩
  have hgint : IntervalIntegrable g volume 0 1 := hg.intervalIntegrable_of_Icc (by norm_num)
  rw [intervalIntegral.integral_sub hgint intervalIntegrable_const,
    intervalIntegral.integral_const] at hpos
  simp only [sub_zero, one_smul, mean, sub_self, lt_self_iff_false] at hpos

/-- A nonpositive centered score cannot have positive Election 1 excess. -/
theorem rankOneExcess_nonpos_of_activation_le (g : ℝ → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam) (hg : ContinuousOn g (Icc 0 1))
    (hbound : UniversalBound g (1 + 2 * lam))
    (s : ℝ) (hs : s ∈ Icc 0 1) (hsbelow : g s < ∫ x in (0 : ℝ)..1, g x)
    (r : ℝ) (hr : r ∈ Icc 0 1) (hrbelow : g r ≤ ∫ x in (0 : ℝ)..1, g x) :
    rankOneExcess lam r ≤ 0 := by
  have h := real_twoPoint_necessary g lam 1 r s hlam hg hbound
    (by constructor <;> norm_num) hr hs hsbelow (by simpa using hrbelow)
  simpa [rankOneExcess] using sub_nonpos.mpr h

/-- Pairing opposite centered scores orders the ratios used to choose the scale. -/
theorem rankOne_ratio_comparison (g : ℝ → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam) (hg : ContinuousOn g (Icc 0 1))
    (hbound : UniversalBound g (1 + 2 * lam))
    (r s : ℝ) (hr : r ∈ Icc 0 1) (hs : s ∈ Icc 0 1)
    (hrabove : (∫ x in (0 : ℝ)..1, g x) < g r)
    (hsbelow : g s < ∫ x in (0 : ℝ)..1, g x) :
    rankOneExcess lam r / (g r - ∫ x in (0 : ℝ)..1, g x) ≤
      rankOneExcess lam s / (g s - ∫ x in (0 : ℝ)..1, g x) := by
  let mean := ∫ x in (0 : ℝ)..1, g x
  let x := g r - mean
  let y := mean - g s
  let theta := y / (x + y)
  have hx : 0 < x := sub_pos.mpr hrabove
  have hy : 0 < y := sub_pos.mpr hsbelow
  have hden : 0 < x + y := add_pos hx hy
  have hden0 : x + y ≠ 0 := ne_of_gt hden
  have htheta : theta ∈ Icc 0 1 := by
    constructor
    · exact le_of_lt (div_pos hy hden)
    · exact (div_le_one hden).mpr (by linarith)
  have hgr : g r = mean + x := by dsimp [x]; ring
  have hgs : g s = mean - y := by dsimp [y]; ring
  have hbalance : theta * g r + (1 - theta) * g s = mean := by
    rw [hgr, hgs]
    dsimp [theta]
    field_simp
    ring
  have h := real_twoPoint_necessary g lam theta r s hlam hg hbound htheta hr hs hsbelow hbalance.le
  have hf : theta * rankOneExcess lam r + (1 - theta) * rankOneExcess lam s ≤ 0 := by
    dsimp [rankOneExcess]
    nlinarith
  have hmul := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hden) hf
  have hfactor : (x + y) * (theta * rankOneExcess lam r + (1 - theta) * rankOneExcess lam s) =
      y * rankOneExcess lam r + x * rankOneExcess lam s := by
    dsimp [theta]
    field_simp
    ring
  rw [hfactor] at hmul
  have hratio : rankOneExcess lam r / x ≤ (-rankOneExcess lam s) / y := by
    apply (div_le_div_iff₀ hx hy).mpr
    nlinarith
  have hsden : g s - mean = -y := by dsimp [y]; ring
  change rankOneExcess lam r / x ≤ rankOneExcess lam s / (g s - mean)
  rw [hsden]
  simpa only [neg_div, div_neg] using hratio

/-- Elementary scalar separation by a bounded supremum of positive-score ratios. -/
theorem exists_positive_scalar_separator (S : Set ℝ) (h f : ℝ → ℝ)
    (rpos rneg : ℝ) (hrpos : rpos ∈ S) (hrneg : rneg ∈ S)
    (hhpos : 0 < h rpos) (hfpos : 0 < f rpos) (hhneg : h rneg < 0)
    (hzero : ∀ r ∈ S, h r = 0 → f r ≤ 0)
    (hcompare : ∀ r ∈ S, ∀ s ∈ S, 0 < h r → h s < 0 → f r / h r ≤ f s / h s) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ S, f r ≤ c * h r := by
  let ratios : Set ℝ := {q | ∃ r ∈ S, 0 < h r ∧ q = f r / h r}
  have hmem : f rpos / h rpos ∈ ratios := ⟨rpos, hrpos, hhpos, rfl⟩
  have hnonempty : ratios.Nonempty := ⟨_, hmem⟩
  have hbdd : BddAbove ratios := by
    refine ⟨f rneg / h rneg, ?_⟩
    rintro q ⟨r, hr, hhr, rfl⟩
    exact hcompare r hr rneg hrneg hhr hhneg
  let c := sSup ratios
  have hc : 0 < c := lt_of_lt_of_le (div_pos hfpos hhpos) (le_csSup hbdd hmem)
  refine ⟨c, hc, ?_⟩
  intro r hr
  rcases lt_trichotomy (h r) 0 with hneg | hzer | hpos
  · have hupper : c ≤ f r / h r := by
      apply csSup_le hnonempty
      rintro q ⟨s, hs, hhs, rfl⟩
      exact hcompare s hs r hr hhs hneg
    have hmul := mul_le_mul_of_nonpos_right hupper (le_of_lt hneg)
    rwa [div_mul_cancel₀ _ (ne_of_lt hneg)] at hmul
  · simpa only [hzer, mul_zero] using hzero r hr hzer
  · have hratio : f r / h r ≤ c := le_csSup hbdd ⟨r, hr, hpos, rfl⟩
    exact (div_le_iff₀ hpos).mp hratio

/-- The normalizing scale and every pointwise bound asserted in the first part
of Lemma 3.1, derived from the universal distortion bound. -/
theorem exists_centered_activation (g : ℝ → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam) (hg : ContinuousOn g (Icc 0 1))
    (hbound : UniversalBound g (1 + 2 * lam)) :
    ∃ c : ℝ, 0 < c ∧
      ContinuousOn (fun r => c * ((∫ u in (0 : ℝ)..1, g u) - g r)) (Icc 0 1) ∧
      (∫ r in (0 : ℝ)..1, c * ((∫ u in (0 : ℝ)..1, g u) - g r)) = 0 ∧
      c * ((∫ u in (0 : ℝ)..1, g u) - g 1) ≤ -1 ∧
      ∀ r ∈ Icc (0 : ℝ) 1, c * ((∫ u in (0 : ℝ)..1, g u) - g r) ≤ lam - r := by
  let mean := ∫ u in (0 : ℝ)..1, g u
  have htop := endpoint_above_mean_of_universalBound g lam hlam hbound
  obtain ⟨s, hs, hsbelow⟩ := exists_rank_below_mean g hg htop
  obtain ⟨c, hc, hsep⟩ := exists_positive_scalar_separator (Icc 0 1)
    (fun r => g r - mean) (rankOneExcess lam) 1 s (by norm_num) hs
    (sub_pos.mpr htop) (by simp) (sub_neg.mpr hsbelow)
    (fun r hr hzero => rankOneExcess_nonpos_of_activation_le g lam hlam hg hbound s hs hsbelow
      r hr (by linarith))
    (fun r hr t ht hpos hneg => rankOne_ratio_comparison g lam hlam hg hbound r t hr ht
      (sub_pos.mp hpos) (sub_neg.mp hneg))
  have hcont : ContinuousOn (fun r => c * (mean - g r)) (Icc 0 1) :=
    continuousOn_const.mul (continuousOn_const.sub hg)
  have hzero : (∫ r in (0 : ℝ)..1, c * (mean - g r)) = 0 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegrable_const
        (hg.intervalIntegrable_of_Icc (by norm_num)), intervalIntegral.integral_const]
    simp [mean]
  have hend : c * (mean - g 1) ≤ -1 := by
    have h := hsep 1 (by norm_num)
    simp only [rankOneExcess_one] at h
    nlinarith
  refine ⟨c, hc, hcont, hzero, hend, ?_⟩
  intro r hr
  have h := hsep r hr
  by_cases hr1 : r = 1
  · subst r
    linarith
  · simp only [rankOneExcess, rankOneGap, if_neg hr1, mul_one] at h
    nlinarith

/-- The centered activation cap forces the strict elementary lower bound λ>1/2.
Strictness comes from the endpoint value, not from a non-strict integral bound. -/
theorem parameter_gt_half_of_universalBound (g : ℝ → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam) (hg : ContinuousOn g (Icc 0 1))
    (hbound : UniversalBound g (1 + 2 * lam)) : 1 / 2 < lam := by
  obtain ⟨c, hc, hcont, hzero, hend, hcap⟩ := exists_centered_activation g lam hlam hg hbound
  let phi := fun r => c * ((∫ u in (0 : ℝ)..1, g u) - g r)
  have hslack : ContinuousOn (fun r => (lam - r) - phi r) (Icc 0 1) :=
    (continuousOn_const.sub continuousOn_id).sub hcont
  have hpos : 0 < ∫ r in (0 : ℝ)..1, ((lam - r) - phi r) := by
    apply intervalIntegral.integral_pos (by norm_num) hslack
    · intro r hr
      exact sub_nonneg.mpr (hcap r ⟨le_of_lt hr.1, hr.2⟩)
    · by_cases hlam0 : lam = 0
      · have h := hcap 0 (by norm_num)
        have hnonneg : ∀ r ∈ Icc (0 : ℝ) 1, phi r ≤ 0 := by
          intro r hr
          have h := hcap r hr
          dsimp [phi]
          linarith [hr.1]
        have hneg : (∫ r in (0 : ℝ)..1, phi r) < 0 := by
          have hn := intervalIntegral.integral_pos (show (0 : ℝ) < 1 by norm_num)
            hcont.neg (fun r hr => neg_nonneg.mpr (hnonneg r ⟨le_of_lt hr.1, hr.2⟩))
            ⟨1, by norm_num, by dsimp [phi]; linarith⟩
          change 0 < ∫ r in (0 : ℝ)..1, -phi r at hn
          rw [intervalIntegral.integral_neg] at hn
          linarith
        exact False.elim (by change (∫ r in (0 : ℝ)..1, phi r) = 0 at hzero; linarith)
      · refine ⟨1, by norm_num, ?_⟩
        dsimp [phi]
        have hp := lt_of_le_of_ne hlam (Ne.symm hlam0)
        linarith
  have hcapint : IntervalIntegrable (fun r : ℝ => lam - r) volume 0 1 :=
    intervalIntegrable_const.sub (Continuous.intervalIntegrable continuous_id _ _)
  have hid : IntervalIntegrable (fun r : ℝ => r) volume 0 1 := continuous_id.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hcapint (hcont.intervalIntegrable_of_Icc (by norm_num)),
    hzero, sub_zero, intervalIntegral.integral_sub intervalIntegrable_const
      hid, intervalIntegral.integral_const,
    integral_id] at hpos
  norm_num at hpos ⊢
  linarith

end OptimalG
