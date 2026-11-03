import OptimalG.Finite
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The threshold telescoping step of Section 5.1

This is a theorem about integrable slice functions, including arbitrary real threshold shifts.
It covers the case where the shift exceeds the total threshold range. The hypotheses connecting
these functions to a stable lottery (packing, layer cake, and the four verifier inequalities)
are not asserted here.
-/

namespace OptimalG

open MeasureTheory Set
open scoped Interval BigOperators

private theorem subinterval_integrable {F : ℝ → ℝ} {a b c d : ℝ}
    (hF : IntervalIntegrable F volume a b) (hab : a ≤ b)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    IntervalIntegrable F volume c d := by
  apply hF.mono_set
  rw [uIcc_of_le hcd, uIcc_of_le hab]
  exact Icc_subset_Icc hac hdb

/-- The exact shifted-integral cancellation behind (5.2), with no discretization. -/
theorem integral_shift_cancellation (F : ℝ → ℝ) (X delta : ℝ)
    (hX : 0 ≤ X) (hd : 0 ≤ delta)
    (hF : IntervalIntegrable F volume (-delta) X) :
    (∫ t in (0 : ℝ)..X, (F (t - delta) - F t)) =
      (∫ t in -delta..0, F t) - (∫ t in X - delta..X, F t) := by
  have htot : -delta ≤ X := by linarith
  have h0X := subinterval_integrable hF htot (by linarith : -delta ≤ 0) hX le_rfl
  have hshift := subinterval_integrable hF htot le_rfl
    (by linarith : -delta ≤ X - delta) (by linarith : X - delta ≤ X)
  have htrans : IntervalIntegrable (fun t => F (t - delta)) volume 0 X := by
    simpa using hshift.comp_sub_right delta
  rw [intervalIntegral.integral_sub htrans h0X,
    intervalIntegral.integral_comp_sub_right]
  simp only [zero_sub]
  exact intervalIntegral.integral_interval_sub_interval_comm hshift h0X
    (subinterval_integrable hF htot le_rfl (by linarith) hX)

/-- An offset slice bounded by a backward potential difference has integral at most λΔ. -/
theorem integral_telescope_bound (L F : ℝ → ℝ) (X delta lam : ℝ)
    (hX : 0 ≤ X) (hd : 0 ≤ delta) (hlam : 0 ≤ lam)
    (hL : IntervalIntegrable L volume 0 X)
    (hF : IntervalIntegrable F volume (-delta) X)
    (hnegative : ∀ t, t < 0 → F t = lam)
    (hnonnegative : ∀ t, 0 ≤ t → 0 ≤ F t)
    (hbound : ∀ t ∈ Icc 0 X, L t ≤ F (t - delta) - F t) :
    (∫ t in (0 : ℝ)..X, L t) ≤ lam * delta := by
  have htot : -delta ≤ X := by linarith
  have h0X := subinterval_integrable hF htot (by linarith : -delta ≤ 0) hX le_rfl
  have hshift := subinterval_integrable hF htot le_rfl
    (by linarith : -delta ≤ X - delta) (by linarith : X - delta ≤ X)
  have htrans : IntervalIntegrable (fun t => F (t - delta)) volume 0 X := by
    simpa using hshift.comp_sub_right delta
  have hle := intervalIntegral.integral_mono_on hX hL (htrans.sub h0X) hbound
  rw [integral_shift_cancellation F X delta hX hd hF] at hle
  have hleft : (∫ t in -delta..0, F t) = lam * delta := by
    calc
      _ = ∫ _t in -delta..(0 : ℝ), lam := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro t ht
        exact hnegative t ht.2
      _ = lam * delta := by rw [intervalIntegral.integral_const]; simp; ring
  have hall : ∀ t, 0 ≤ F t := by
    intro t
    rcases lt_or_ge t 0 with ht | ht
    · rw [hnegative t ht]; exact hlam
    · exact hnonnegative t ht
  have hright : 0 ≤ ∫ t in X - delta..X, F t :=
    intervalIntegral.integral_nonneg_of_forall (by linarith) hall
  rw [hleft] at hle
  linarith

/-- Extension by the initial potential value, as used immediately after (5.2). -/
noncomputable def extendedPotential (W q : ℝ → ℝ) (lam t : ℝ) : ℝ :=
  if t < 0 then lam else W (q t)

/-- The two slice inequalities imply the backward potential-difference bound.
The separation property `hz` is the second inequality of (5.1). -/
theorem slice_bound_to_difference
    (L W q z : ℝ → ℝ) (lam delta s t : ℝ)
    (ht : 0 ≤ t)
    (hfirst : L t ≤ lam - W (q t))
    (hsecond : ∀ r, z t ≤ r → r ≤ s → L t ≤ W r - W (q t))
    (hq : ∀ r, 0 ≤ r → q r ≤ s)
    (hz : ∀ r, 0 ≤ r → z (r + delta) ≤ q r) :
    L t ≤ extendedPotential W q lam (t - delta) - extendedPotential W q lam t := by
  simp only [extendedPotential, if_neg (not_lt.mpr ht)]
  by_cases htd : t - delta < 0
  · rw [if_pos htd]
    exact hfirst
  · rw [if_neg htd]
    have htd' : 0 ≤ t - delta := le_of_not_gt htd
    apply hsecond (q (t - delta))
    · simpa using hz (t - delta) htd'
    · exact hq (t - delta) htd'

/-- Integration commutes with finite weighted averaging. -/
theorem integral_expectation {V : Type*} [Fintype V]
    (w : V → ℝ) (f : V → ℝ → ℝ) (a b : ℝ)
    (hf : ∀ v, IntervalIntegrable (f v) volume a b) :
    (∫ t in a..b, expectation w (fun v => f v t)) =
      expectation w (fun v => ∫ t in a..b, f v t) := by
  unfold expectation
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro v _
    exact intervalIntegral.integral_const_mul (w v) (f v)
  · intro v _
    exact (hf v).const_mul (w v)

/-- Averaging the telescoping bound yields the target running-minimum inequality.
This theorem checks the integration/averaging argument; it does not supply the slice hypotheses. -/
theorem averaged_slice_bound {V : Type*} [Fintype V]
    (w delta : V → ℝ) (q L F : V → ℝ → ℝ) (X lam : ℝ)
    (hw : ∀ v, 0 ≤ w v) (hd : ∀ v, 0 ≤ delta v)
    (hX : 0 ≤ X) (hlam : 0 ≤ lam)
    (hq : ∀ v, IntervalIntegrable (q v) volume 0 X)
    (hL : ∀ v, IntervalIntegrable (L v) volume 0 X)
    (hF : ∀ v, IntervalIntegrable (F v) volume (-delta v) X)
    (hnegative : ∀ v t, t < 0 → F v t = lam)
    (hnonnegative : ∀ v t, 0 ≤ t → 0 ≤ F v t)
    (hoffset : ∀ t ∈ Icc 0 X,
      expectation w (fun v => q v t) ≤ expectation w (fun v => L v t))
    (hbound : ∀ v t, t ∈ Icc 0 X → L v t ≤ F v (t - delta v) - F v t) :
    expectation w (fun v => ∫ t in (0 : ℝ)..X, q v t) ≤
      lam * expectation w delta := by
  have hintq : IntervalIntegrable (fun t => expectation w (fun v => q v t)) volume 0 X := by
    have hf : (fun t => expectation w (fun v => q v t)) =
        (∑ v, fun t => w v * q v t) := by
      funext t
      simp [expectation]
    rw [hf]
    exact IntervalIntegrable.sum Finset.univ (fun v _ => (hq v).const_mul (w v))
  have hintL : IntervalIntegrable (fun t => expectation w (fun v => L v t)) volume 0 X := by
    have hf : (fun t => expectation w (fun v => L v t)) =
        (∑ v, fun t => w v * L v t) := by
      funext t
      simp [expectation]
    rw [hf]
    exact IntervalIntegrable.sum Finset.univ (fun v _ => (hL v).const_mul (w v))
  have hfirst := intervalIntegral.integral_mono_on hX hintq hintL hoffset
  rw [integral_expectation w q 0 X hq, integral_expectation w L 0 X hL] at hfirst
  calc
    _ ≤ expectation w (fun v => ∫ t in (0 : ℝ)..X, L v t) := hfirst
    _ ≤ expectation w (fun v => lam * delta v) := by
      apply expectation_mono hw
      intro v
      exact integral_telescope_bound (L v) (F v) X (delta v) lam hX (hd v) hlam
        (hL v) (hF v) (hnegative v) (hnonnegative v) (hbound v)
    _ = lam * expectation w delta := expectation_smul w delta lam

end OptimalG
