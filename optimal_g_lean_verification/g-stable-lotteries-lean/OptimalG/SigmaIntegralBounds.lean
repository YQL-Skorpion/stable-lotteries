import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-! Integral cone estimates for the nonnegative decreasing slack score in C.3.
The slope premise is a finite increment bound, so it also applies at joins of
piecewise smooth scores. -/
namespace OptimalG
open Set MeasureTheory

private theorem integral_descending_line (v k q a b : ℝ) :
    (∫ r in a..b,v+k*(q-r))=(v+k*q)*(b-a)-k*(b^2-a^2)/2 := by
  have hd (r : ℝ) : HasDerivAt (fun r => (v+k*q)*r-k*r^2/2) (v+k*(q-r)) r := by
    convert! (((hasDerivAt_id r).const_mul (v+k*q)).sub
      (((hasDerivAt_id r).pow 2).const_mul k |>.div_const 2)) using 1 <;> (try simp only [id_eq]) <;> first | rfl | ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    ((by fun_prop : Continuous (fun r => v+k*(q-r))).intervalIntegrable a b)]
  ring

/-- Ordinary derivative bounds imply the finite slope conditions consumed by
all subsequent area estimates. -/
theorem sigma_shape_of_derivative_bounds {sigma ds : ℝ → ℝ} {c t k : ℝ}
    (hc : ContinuousOn sigma (Icc c t))
    (hd : ∀ r ∈ Ioo c t,HasDerivAt sigma (ds r) r)
    (hb : ∀ r ∈ Ioo c t,-k≤ds r ∧ ds r≤0) :
    AntitoneOn sigma (Icc c t) ∧
      ∀ a ∈ Icc c t,∀ b ∈ Icc c t,a≤b → sigma a-sigma b≤k*(b-a) := by
  have hanti : AntitoneOn sigma (Icc c t) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc c t) hc (f':=ds)
    · intro r hr
      exact (hd r (by simpa using hr)).hasDerivWithinAt
    · intro r hr
      exact (hb r (by simpa using hr)).2
  have hmono : MonotoneOn (fun r => sigma r+k*r) (Icc c t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc c t)
      (hc.add (continuousOn_const.mul continuousOn_id)) (f':=fun r => ds r+k)
    · intro r hr
      have hder := (hd r (by simpa using hr)).add ((hasDerivAt_id r).const_mul k)
      convert! hder.hasDerivWithinAt using 1 <;> simp
    · intro r hr
      have hh := (hb r (by simpa using hr)).1
      linarith
  refine ⟨hanti,?_⟩
  intro a ha b hb hab
  have hh := hmono ha hb hab
  nlinarith

/-- The largest possible prefix area with prescribed endpoint scores is the
rectangle followed by the steepest permitted descending line. -/
theorem sigma_prefix_upper {sigma : ℝ → ℝ} {c q k : ℝ}
    (hcq : c≤q) (hk : 0<k) (hc : ContinuousOn sigma (Icc c q))
    (ha : AntitoneOn sigma (Icc c q))
    (hslope : ∀ r ∈ Icc c q,sigma r-sigma q≤k*(q-r)) :
    (∫ r in c..q,sigma r)≤sigma c*(q-c)-(sigma c-sigma q)^2/(2*k) := by
  let s := sigma c
  let v := sigma q
  let cut := q-(s-v)/k
  have hsv : v≤s := ha (left_mem_Icc.mpr hcq) (right_mem_Icc.mpr hcq) hcq
  have hdrop : s-v≤k*(q-c) := hslope c (left_mem_Icc.mpr hcq)
  have hcut : cut ∈ Icc c q := by
    dsimp [cut]
    have hdiv : (s-v)/k≤q-c := (div_le_iff₀ hk).mpr (by nlinarith)
    have hn : 0≤(s-v)/k := div_nonneg (sub_nonneg.mpr hsv) hk.le
    constructor <;> linarith
  have hi1 := (hc.mono (Icc_subset_Icc le_rfl hcut.2)).intervalIntegrable_of_Icc (μ := volume) hcut.1
  have hi2 := (hc.mono (Icc_subset_Icc hcut.1 le_rfl)).intervalIntegrable_of_Icc (μ := volume) hcut.2
  have h1 : (∫ r in c..cut,sigma r)≤s*(cut-c) := by
    have hh := intervalIntegral.integral_mono_on hcut.1 hi1
      (intervalIntegrable_const (c:=s)) (fun r hr =>
        ha (left_mem_Icc.mpr hcq) ⟨hr.1,hr.2.trans hcut.2⟩ hr.1)
    simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_comm] using hh
  have h2 : (∫ r in cut..q,sigma r)≤(v+k*q)*(q-cut)-k*(q^2-cut^2)/2 := by
    rw [← integral_descending_line v k q cut q]
    apply intervalIntegral.integral_mono_on hcut.2 hi2
      ((by fun_prop : Continuous (fun r => v+k*(q-r))).intervalIntegrable cut q)
    intro r hr
    have hh := hslope r ⟨hcut.1.trans hr.1,hr.2⟩
    dsimp [v]
    linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  calc
    _≤s*(cut-c)+((v+k*q)*(q-cut)-k*(q^2-cut^2)/2) := add_le_add h1 h2
    _=sigma c*(q-c)-(sigma c-sigma q)^2/(2*k) := by
      dsimp [cut,s,v]
      field_simp
      ring

/-- Nonnegativity and the slope bound force a triangle of area v²/(2k)
after any point of height v, before the terminal zero. -/
theorem sigma_tail_lower {sigma : ℝ → ℝ} {q t k : ℝ}
    (hqt : q≤t) (hk : 0<k) (hc : ContinuousOn sigma (Icc q t))
    (hn : ∀ r ∈ Icc q t,0≤sigma r) (ht : sigma t=0)
    (hslope : ∀ r ∈ Icc q t,sigma q-sigma r≤k*(r-q)) :
    (sigma q)^2/(2*k)≤∫ r in q..t,sigma r := by
  let v := sigma q
  let cut := q+v/k
  have hv : 0≤v := hn q (left_mem_Icc.mpr hqt)
  have hdrop : v≤k*(t-q) := by
    have hh := hslope t (right_mem_Icc.mpr hqt)
    simpa only [ht,sub_zero] using hh
  have hcut : cut ∈ Icc q t := by
    dsimp [cut]
    have hdiv : v/k≤t-q := (div_le_iff₀ hk).mpr (by nlinarith)
    have hn' := div_nonneg hv hk.le
    constructor <;> linarith
  have hi1 := (hc.mono (Icc_subset_Icc le_rfl hcut.2)).intervalIntegrable_of_Icc (μ := volume) hcut.1
  have hi2 := (hc.mono (Icc_subset_Icc hcut.1 le_rfl)).intervalIntegrable_of_Icc (μ := volume) hcut.2
  have h1 : v^2/(2*k)≤∫ r in q..cut,sigma r := by
    have hline : (∫ r in q..cut,v+k*(q-r))=v^2/(2*k) := by
      rw [integral_descending_line]
      dsimp [cut]
      field_simp
      ring
    rw [← hline]
    apply intervalIntegral.integral_mono_on hcut.1
      ((by fun_prop : Continuous (fun r => v+k*(q-r))).intervalIntegrable q cut) hi1
    intro r hr
    have hh := hslope r ⟨hr.1,hr.2.trans hcut.2⟩
    dsimp [v]
    linarith
  have h2 : 0≤∫ r in cut..t,sigma r := intervalIntegral.integral_nonneg hcut.2
    (fun r hr => hn r ⟨hcut.1.trans hr.1,hr.2⟩)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  exact h1.trans (le_add_of_nonneg_right h2)

/-- The endpoint rectangle is an upper bound for the remaining slack area. -/
theorem sigma_tail_upper {sigma : ℝ → ℝ} {q t : ℝ}
    (hqt : q≤t) (hc : ContinuousOn sigma (Icc q t))
    (ha : AntitoneOn sigma (Icc q t)) :
    (∫ r in q..t,sigma r)≤sigma q*(t-q) := by
  have hh := intervalIntegral.integral_mono_on hqt (hc.intervalIntegrable_of_Icc (μ := volume) hqt)
    (intervalIntegrable_const (c:=sigma q)) (fun r hr =>
      ha (left_mem_Icc.mpr hqt) hr hr.1)
  simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_comm] using hh

end OptimalG
