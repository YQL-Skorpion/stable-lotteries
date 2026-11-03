import OptimalG.Certificates.IntegerRounded
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! A linear-size certificate for all suffix integrals of a finite ordered
partition. The checker uses only integer interval addition/subset tests and
endpoint comparisons. Actual cell integral enclosures are separate inputs. -/
namespace OptimalG.Certificates
open Set MeasureTheory

structure IntegralCell where
  lo : ℚ
  hi : ℚ
  mass : IntegerInterval
  future : IntegerInterval
  deriving DecidableEq, Repr

def totalBox : List IntegralCell → IntegerInterval
  | [] => ⟨0,0⟩
  | c::_ => c.mass.addRounded c.future

/-- Each proposed future interval contains the next cell's total interval.
In particular the final future interval must contain zero. -/
def cumulativeIntegralCheck (s : ℕ) (start finish : ℚ) : List IntegralCell → Bool
  | [] => decide (start=finish)
  | c::cs => decide (c.lo=start ∧ c.lo<c.hi) &&
      ((totalBox cs).subsetCheck c.future && cumulativeIntegralCheck s c.hi finish cs)

/-- Accepted cumulative proposals enclose the whole integral and every
future integral. Integrability is propagated across the partition as well. -/
theorem cumulativeIntegralCheck_sound {s : ℕ} {f : ℝ→ℝ}
    {start finish : ℚ} {cells : List IntegralCell}
    (hcheck : cumulativeIntegralCheck s start finish cells=true)
    (hcells : ∀ c ∈ cells,
      IntervalIntegrable f volume (c.lo:ℝ) (c.hi:ℝ) ∧
      c.mass.Contains s (∫ r in (c.lo:ℝ)..(c.hi:ℝ),f r)) :
    IntervalIntegrable f volume (start:ℝ) (finish:ℝ) ∧
    (totalBox cells).Contains s (∫ r in (start:ℝ)..(finish:ℝ),f r) ∧
    ∀ c ∈ cells,IntervalIntegrable f volume (c.hi:ℝ) (finish:ℝ) ∧
      c.future.Contains s (∫ r in (c.hi:ℝ)..(finish:ℝ),f r) := by
  induction cells generalizing start with
  | nil =>
    have he : start=finish := by simpa only [cumulativeIntegralCheck,decide_eq_true_eq] using hcheck
    subst start
    simp [totalBox,IntegerInterval.Contains]
  | cons c cs ih =>
    have hcheck' : (c.lo=start ∧ c.lo<c.hi) ∧
        (totalBox cs).subsetCheck c.future=true ∧ cumulativeIntegralCheck s c.hi finish cs=true := by
      simpa only [cumulativeIntegralCheck,Bool.and_eq_true,decide_eq_true_eq] using hcheck
    obtain ⟨hcover,hfuture,htail⟩ := hcheck'
    obtain ⟨hint,hmass⟩ := hcells c (by simp)
    obtain ⟨htailInt,htailMass,hfutureTail⟩ := ih htail (fun d hd => hcells d (by simp [hd]))
    have hfutureMass := IntegerInterval.subsetCheck_sound htailMass hfuture
    have hsum := IntegerInterval.addRounded_contains hmass hfutureMass
    rw [intervalIntegral.integral_add_adjacent_intervals hint htailInt] at hsum
    rw [←hcover.1]
    refine ⟨hint.trans htailInt,hsum,?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with he|hd
    · subst d
      exact ⟨htailInt,hfutureMass⟩
    · exact hfutureTail d hd

/-- A bounded integrand gives a common enclosure for every partial suffix
of a cell. The bounds allow either sign, including a zero-length suffix. -/
theorem partial_cell_integral_bounds {f : ℝ→ℝ} {a b r L U : ℝ}
    (hr : r ∈ Icc a b) (hf : IntervalIntegrable f volume a b)
    (hbound : ∀ᵐ x ∂volume.restrict (Icc a b),L≤f x ∧ f x≤U) :
    min 0 ((b-a)*L)≤(∫ x in r..b,f x) ∧
      (∫ x in r..b,f x)≤max 0 ((b-a)*U) := by
  have hab : a≤b := hr.1.trans hr.2
  have hi : IntervalIntegrable f volume r b := hf.mono_set (by
    rw [uIcc_of_le hr.2,uIcc_of_le hab]
    exact Icc_subset_Icc hr.1 le_rfl)
  have hsub : ∀ᵐ x ∂volume.restrict (Icc r b),L≤f x ∧ f x≤U :=
    ae_mono (Measure.restrict_mono (Icc_subset_Icc hr.1 le_rfl) le_rfl) hbound
  have hlo := intervalIntegral.integral_mono_ae_restrict hr.2
    (intervalIntegrable_const (c:=L)) hi (hsub.mono (fun x hx => hx.1))
  have hhi := intervalIntegral.integral_mono_ae_restrict hr.2 hi
    (intervalIntegrable_const (c:=U)) (hsub.mono (fun x hx => hx.2))
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hlo hhi
  constructor
  · apply le_trans _ hlo
    by_cases hL : 0≤L
    · exact (min_le_left _ _).trans (mul_nonneg (sub_nonneg.mpr hr.2) hL)
    · exact (min_le_right _ _).trans
        (mul_le_mul_of_nonpos_right (by linarith only [hr.1]) (le_of_not_ge hL))
  · apply le_trans hhi
    by_cases hU : 0≤U
    · exact (mul_le_mul_of_nonneg_right (by linarith only [hr.1]) hU).trans (le_max_right _ _)
    · exact (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr.2)
        (le_of_not_ge hU)).trans (le_max_left _ _)

end OptimalG.Certificates
