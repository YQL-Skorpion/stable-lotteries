import OptimalG.VariationalContactLocation
import OptimalG.TailContact
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Before cap replacement, admissibility alone controls the cap slope up to
any genuine interior contact. No numerical tube hypothesis is used here. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem capScore_hasDerivAt (lam S r : ℝ) (hr : r ≠ 1) :
    HasDerivAt (capScore lam S) (-2*lam*S/(1-r)^3) r := by
  have hh : 1-r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  have hi := ((hasDerivAt_const r 1).sub (hasDerivAt_id r)).pow 2
  have hd := (hasDerivAt_const r (lam/2)).sub ((hasDerivAt_const r (lam*S)).div hi (pow_ne_zero 2 hh))
  change HasDerivAt (capScore lam S)
    (0-(0*(1-r)^2-lam*S*(2*(1-r)^1*(0-1)))/((1-r)^2)^2) r at hd
  have he : 0-(0*(1-r)^2-lam*S*(2*(1-r)^1*(0-1)))/((1-r)^2)^2 = -2*lam*S/(1-r)^3 := by
    field_simp
    ring
  rwa [he] at hd

theorem Admissible.capScore_pos {lam r : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hr : r ∈ Icc ell tEnd) : 0 < capScore lam d.S r := by
  have hL : 0 < lam := by have hh := hd.1.1; norm_num [lambdaLo] at hh; linarith
  have hS : d.S ≤ (3:ℝ)/100 := by linarith [hd.slack_upper]
  have hr1 : r ≤ (385:ℝ)/1000 := hr.2
  have hden : 0 < (1-r)^2 := sq_pos_of_pos (by linarith)
  have hfrac : d.S/(1-r)^2 < (1:ℝ)/2 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [sq_nonneg (r-385/1000)]
  unfold capScore
  rw [mul_div_assoc]
  nlinarith [mul_pos hL (sub_pos.mpr hfrac)]

theorem Admissible.capScore_gap_monotone {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) : MonotoneOn (fun r => capScore lam d.S r-(lam-r)) (Icc ell tEnd) := by
  have hL0 : 0 ≤ lam := by have hh := hd.1.1; norm_num [lambdaLo] at hh; linarith
  have hL1 : lam ≤ (57:ℝ)/100 := by have hh := hd.1.2; norm_num [lambdaHi] at hh; linarith
  have hS0 : 0 ≤ d.S := by linarith [hd.slack_lower]
  have hS1 : d.S ≤ (3:ℝ)/100 := by linarith [hd.slack_upper]
  have hder (r : ℝ) (hr : r ∈ Icc ell tEnd) :
      HasDerivAt (fun r => capScore lam d.S r-(lam-r)) (1-2*lam*d.S/(1-r)^3) r := by
    have hr1 : r ≤ (385:ℝ)/1000 := hr.2
    have hh := (capScore_hasDerivAt lam d.S r (by linarith)).sub
      ((hasDerivAt_const r lam).sub (hasDerivAt_id r))
    change HasDerivAt (fun r => capScore lam d.S r-(lam-r))
      (-2*lam*d.S/(1-r)^3-(0-1)) r at hh
    convert hh using 1 <;> ring
  apply monotoneOn_of_deriv_nonneg (convex_Icc ell tEnd)
    (fun r hr => (hder r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hder r (interior_subset hr)).differentiableAt.differentiableWithinAt)
  intro r hr
  have hr1 : r ≤ (385:ℝ)/1000 := (interior_subset hr).2
  rw [(hder r (interior_subset hr)).deriv]
  have hden0 : 0 < (1-r)^3 := pow_pos (by linarith) _
  have hden : (6/10:ℝ)^3 ≤ (1-r)^3 := pow_le_pow_left₀ (by norm_num) (by linarith) _
  have hLS := mul_le_mul hL1 hS1 hS0 (by norm_num : (0:ℝ) ≤ 57/100)
  have hfrac : 2*lam*d.S/(1-r)^3 ≤ 1 := by
    apply (div_le_iff₀ hden0).mpr
    norm_num at hden
    nlinarith only [hLS,hden]
  linarith

private theorem right_endpoint_min_derivative_nonpos {f : ℝ → ℝ} {a b v : ℝ}
    (hab : a < b) (hmin : IsMinOn f (Icc a b) b) (hd : HasDerivAt f v b) : v ≤ 0 := by
  have ht : a-b ∈ posTangentConeAt (Icc a b) b :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc a b).segment_subset ⟨hab.le,le_rfl⟩ ⟨le_rfl,hab.le⟩)
  have hh := hmin.localize.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt ht
  change 0 ≤ (a-b)*v at hh
  nlinarith

theorem Admissible.capScore_le_line_at_contact {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : c ∈ Ioc ell tEnd)
    (heq : lowPrimitive lam d c = cap lam d.S c) : capScore lam d.S c ≤ lam-c := by
  have hc' : c ∈ Icc ell tEnd := ⟨hc.1.le,hc.2⟩
  have hmin : IsMinOn (fun r => cap lam d.S r-quadratic lam r) (Icc ell c) c := by
    intro r hr
    have hr' : r ∈ Icc ell tEnd := ⟨hr.1,hr.2.trans hc.2⟩
    have hbounds : ∀ᵐ u ∂volume.restrict (Icc r c), d.phi u ≤ lam-u :=
      ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hr.1 hc.2)
        (hd.2.2.2.1.mono (fun _ h => h.2))
    have hi := intervalIntegral.integral_mono_ae_restrict hr.2
      (hd.intervalIntegrable hr.1 hr.2 hc.2)
      ((continuous_const.sub continuous_id).intervalIntegrable r c) hbounds
    change (∫ u in r..c,d.phi u) ≤ ∫ u in r..c,lam-u at hi
    rw [integral_line,← hd.lowPrimitive_sub hr' hc',heq] at hi
    have hh := hd.lowPrimitive_le_cap hr'
    dsimp
    linarith
  have hc1 : c ≠ 1 := by have hh := hc.2; norm_num [tEnd] at hh; linarith
  have hv := right_endpoint_min_derivative_nonpos hc.1 hmin
    ((cap_hasDerivAt lam d.S c hc1).sub (quadratic_hasDerivAt lam c))
  linarith

theorem Admissible.capScore_bounds_before_contact {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : c ∈ Ioc ell tEnd)
    (heq : lowPrimitive lam d c = cap lam d.S c) :
    ∀ r ∈ Icc ell c, 0 < capScore lam d.S r ∧ capScore lam d.S r ≤ lam-r := by
  intro r hr
  have hr' : r ∈ Icc ell tEnd := ⟨hr.1,hr.2.trans hc.2⟩
  have hh := hd.capScore_gap_monotone hr' ⟨hc.1.le,hc.2⟩ hr.2
  have hcscore := hd.capScore_le_line_at_contact hc heq
  exact ⟨hd.capScore_pos hr',by linarith⟩

end OptimalG.Variational
