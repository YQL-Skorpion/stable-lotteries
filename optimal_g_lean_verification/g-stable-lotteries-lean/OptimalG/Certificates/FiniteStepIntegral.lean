import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! Exact integral semantics for a finite ordered piecewise-constant function.
The selector assigns each internal endpoint to the interval on its left.
The endpoint convention has no effect on the integral. -/
namespace OptimalG.Certificates
open Set MeasureTheory

def stepCoverCheck {α : Type*} (lo hi : α → ℚ) (start finish : ℚ) : List α → Bool
  | [] => decide (start = finish)
  | c :: cs => decide (lo c = start ∧ lo c < hi c) &&
      stepCoverCheck lo hi (hi c) finish cs

theorem stepCoverCheck_append {α : Type*} {lo hi : α → ℚ}
    {start middle finish : ℚ} {xs ys : List α}
    (hx : stepCoverCheck lo hi start middle xs = true)
    (hy : stepCoverCheck lo hi middle finish ys = true) :
    stepCoverCheck lo hi start finish (xs ++ ys) = true := by
  induction xs generalizing start with
  | nil =>
    have he : start = middle := by simpa only [stepCoverCheck, decide_eq_true_eq] using hx
    simpa only [he, List.nil_append] using hy
  | cons c cs ih =>
    have hh : (lo c = start ∧ lo c < hi c) ∧
        stepCoverCheck lo hi (hi c) middle cs = true := by
      simpa only [stepCoverCheck, Bool.and_eq_true, decide_eq_true_eq] using hx
    simp only [List.cons_append, stepCoverCheck, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hh.1, ih hh.2⟩

noncomputable def finiteStep {α : Type*} (hi : α → ℚ) (value : α → ℝ) :
    List α → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => if x ≤ (hi c : ℝ) then value c else finiteStep hi value cs x

theorem stepCoverCheck_order {α : Type*} {lo hi : α → ℚ}
    {start finish : ℚ} {cells : List α}
    (hc : stepCoverCheck lo hi start finish cells = true) : start ≤ finish := by
  induction cells generalizing start with
  | nil =>
    have he : start = finish := by simpa only [stepCoverCheck, decide_eq_true_eq] using hc
    exact he.le
  | cons c cs ih =>
    have hh : (lo c = start ∧ lo c < hi c) ∧
        stepCoverCheck lo hi (hi c) finish cs = true := by
      simpa only [stepCoverCheck, Bool.and_eq_true, decide_eq_true_eq] using hc
    exact hh.1.1 ▸ hh.1.2.le.trans (ih hh.2)

theorem stepCoverCheck_mem_bounds {α : Type*} {lo hi : α → ℚ}
    {start finish : ℚ} {cells : List α}
    (hc : stepCoverCheck lo hi start finish cells = true) {c : α} (hm : c ∈ cells) :
    start ≤ lo c ∧ hi c ≤ finish := by
  induction cells generalizing start with
  | nil => simp at hm
  | cons d ds ih =>
    have hh : (lo d = start ∧ lo d < hi d) ∧
        stepCoverCheck lo hi (hi d) finish ds = true := by
      simpa only [stepCoverCheck, Bool.and_eq_true, decide_eq_true_eq] using hc
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨hh.1.1.ge, stepCoverCheck_order hh.2⟩
    · obtain ⟨hlo, hhi⟩ := ih hh.2 hm
      exact ⟨hh.1.1 ▸ hh.1.2.le.trans hlo, hhi⟩

theorem stepCoverCheck_cover {α : Type*} {lo hi : α → ℚ}
    {start finish : ℚ} {cells : List α}
    (hc : stepCoverCheck lo hi start finish cells = true) {x : ℝ}
    (hx : x ∈ Ioc (start : ℝ) (finish : ℝ)) :
    ∃ c ∈ cells, x ∈ Ioc (lo c : ℝ) (hi c : ℝ) := by
  induction cells generalizing start with
  | nil =>
    have he : start = finish := by simpa only [stepCoverCheck, decide_eq_true_eq] using hc
    rw [he] at hx
    exact (not_lt_of_ge hx.2 hx.1).elim
  | cons c cs ih =>
    have hh : (lo c = start ∧ lo c < hi c) ∧
        stepCoverCheck lo hi (hi c) finish cs = true := by
      simpa only [stepCoverCheck, Bool.and_eq_true, decide_eq_true_eq] using hc
    by_cases hlast : x ≤ (hi c : ℝ)
    · exact ⟨c, by simp, ⟨by simpa only [hh.1.1] using hx.1, hlast⟩⟩
    · obtain ⟨d, hd, hxd⟩ := ih hh.2 ⟨lt_of_not_ge hlast, hx.2⟩
      exact ⟨d, by simp [hd], hxd⟩

theorem finiteStep_eq_of_mem {α : Type*} {lo hi : α → ℚ} {value : α → ℝ}
    {start finish : ℚ} {cells : List α}
    (hc : stepCoverCheck lo hi start finish cells = true) {c : α} (hm : c ∈ cells)
    {x : ℝ} (hx : x ∈ Ioc (lo c : ℝ) (hi c : ℝ)) :
    finiteStep hi value cells x = value c := by
  induction cells generalizing start with
  | nil => simp at hm
  | cons d ds ih =>
    have hh : (lo d = start ∧ lo d < hi d) ∧
        stepCoverCheck lo hi (hi d) finish ds = true := by
      simpa only [stepCoverCheck, Bool.and_eq_true, decide_eq_true_eq] using hc
    rcases List.mem_cons.mp hm with rfl | hm
    · simp only [finiteStep, if_pos hx.2]
    · have hb := (stepCoverCheck_mem_bounds hh.2 hm).1
      have hb' : (hi d : ℝ) ≤ lo c := by exact_mod_cast hb
      rw [finiteStep, if_neg (by linarith only [hb', hx.1])]
      exact ih hh.2 hm

/-- Every accepted partition defines an integrable step function with the
expected exact area. No regularity of an unrelated integrand is assumed. -/
theorem finiteStep_integral {α : Type*} {lo hi : α → ℚ} (value : α → ℝ)
    {start finish : ℚ} {cells : List α}
    (hc : stepCoverCheck lo hi start finish cells = true) :
    IntervalIntegrable (finiteStep hi value cells) volume (start : ℝ) (finish : ℝ) ∧
      (∫ x in (start : ℝ)..(finish : ℝ), finiteStep hi value cells x) =
        (cells.map fun c => ((hi c : ℝ) - lo c) * value c).sum := by
  induction cells generalizing start with
  | nil =>
    have he : start = finish := by simpa only [stepCoverCheck, decide_eq_true_eq] using hc
    subst start
    simp
  | cons c cs ih =>
    have hh : (lo c = start ∧ lo c < hi c) ∧
        stepCoverCheck lo hi (hi c) finish cs = true := by
      simpa only [stepCoverCheck, Bool.and_eq_true, decide_eq_true_eq] using hc
    obtain ⟨htail, htailEq⟩ := ih hh.2
    have hfirstOrder : (start : ℝ) ≤ hi c := by exact_mod_cast (hh.1.1 ▸ hh.1.2.le)
    have htailOrder : (hi c : ℝ) ≤ finish := by exact_mod_cast stepCoverCheck_order hh.2
    have hfirst : EqOn (fun _ : ℝ => value c) (finiteStep hi value (c :: cs))
        (uIoo (start : ℝ) (hi c : ℝ)) := by
      rw [uIoo_of_le hfirstOrder]
      intro x hx
      simp only [finiteStep, if_pos hx.2.le]
    have hrest : EqOn (finiteStep hi value cs) (finiteStep hi value (c :: cs))
        (uIoo (hi c : ℝ) (finish : ℝ)) := by
      rw [uIoo_of_le htailOrder]
      intro x hx
      simp only [finiteStep, if_neg (not_le.mpr hx.1)]
    have hfirstInt := (intervalIntegrable_const (μ := volume) (c := value c)).congr_uIoo hfirst
    have hrestInt := htail.congr_uIoo hrest
    refine ⟨hfirstInt.trans hrestInt, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hfirstInt hrestInt,
      ← intervalIntegral.integral_congr_uIoo hfirst,
      ← intervalIntegral.integral_congr_uIoo hrest,
      htailEq, intervalIntegral.integral_const]
    simp only [List.map_cons, List.sum_cons, smul_eq_mul, ← hh.1.1]

theorem finiteStep_integral_rat {α : Type*} {lo hi : α → ℚ} (value : α → ℚ)
    {start finish : ℚ} {cells : List α}
    (hc : stepCoverCheck lo hi start finish cells = true) :
    (∫ x in (start : ℝ)..(finish : ℝ), finiteStep hi (fun c => (value c : ℝ)) cells x) =
      ((cells.map fun c => (hi c - lo c) * value c).sum : ℚ) := by
  rw [(finiteStep_integral (fun c => (value c : ℝ)) hc).2]
  clear hc
  induction cells with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, Rat.cast_sub, ih]

end OptimalG.Certificates
