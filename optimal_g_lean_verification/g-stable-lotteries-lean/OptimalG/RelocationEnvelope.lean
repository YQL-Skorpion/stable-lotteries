import OptimalG.RelocationBinary
import OptimalG.RunningEnvelopeRecovery
import OptimalG.EnvelopeRepair

/-! The actual twice-relocated primitive supplies every input of the repaired
running-envelope construction, including endpoint domination and retention of
the original score on the control ranks. -/
namespace OptimalG.Relocation
open Set MeasureTheory Filter Variational
open scoped NNReal Topology

private theorem variational_range {lam : ℝ} (hL : Certificates.Compact.LambdaRange lam) :
    lam ∈ Icc lambdaLo lambdaHi := by
  norm_num [lambdaLo,lambdaHi,Certificates.Compact.LambdaRange] at *
  exact hL

variable {lam : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass lam phi)
include h

theorem finalScalar_range (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) : Certificates.Compact.ScalarRange (finalScalar lam phi) := by
  refine ⟨finalScalar_lower h hL hLP,?_⟩
  have hu := finalScalar_upper h hL hLP
  unfold universalScalarUpper Certificates.Compact.scalarUpper at *
  linarith [hL.2]

theorem finalScalar_admissible_upper (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) : finalScalar lam phi ≤ slackUpper lam := by
  convert! finalScalar_upper h hL hLP using 1 <;>
    norm_num [universalScalarUpper,slackUpper,lambdaHi]

theorem secondExtended_low_formula (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {r : ℝ} (hr : r ∈ Icc (0.245 : ℝ) 0.38) :
    secondExtendedPrimitive lam phi r = extendedPrimitive phi r + prefixGain lam phi := by
  rw [secondExtendedPrimitive,second_low_eq h hL hLP (by linarith [hr.2]),first_low_eq h hL hLP hr]
  ring

theorem secondExtended_middle_formula (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {r : ℝ} (hr : r ∈ Icc xHi zStart) :
    secondExtendedPrimitive lam phi r = quadratic lam r-finalScalar lam phi := by
  have hr' : r ∈ Icc (0.38 : ℝ) 0.775 := by
    convert! hr using 1 <;> norm_num [xHi,zStart]
  rw [secondExtended_eq lam phi ⟨by linarith [hr'.1],by linarith [hr'.2]⟩,
    secondPrimitive_middle h hL hLP hr']
  rfl

theorem secondExtended_increment (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {x y : ℝ}
    (hx : x ∈ Icc ell tEnd) (hy : y ∈ Icc ell tEnd) (hxy : x ≤ y) :
    secondExtendedPrimitive lam phi y-secondExtendedPrimitive lam phi x ≤
      quadratic lam y-quadratic lam x := by
  have hxI : x ∈ Icc (0 : ℝ) 1 := by
    norm_num [ell,tEnd] at hx
    constructor <;> linarith [hx.1,hx.2]
  have hyI : y ∈ Icc (0 : ℝ) 1 := by
    norm_num [ell,tEnd] at hy
    constructor <;> linarith [hy.1,hy.2]
  rw [secondExtended_eq lam phi hyI,secondExtended_eq lam phi hxI]
  exact retainedSlack_primitive_increment (second_monotone h hL hLP) hxy

omit h in
private theorem cap_difference_local (lam S p q : ℝ) (hp : p ≠ 1) (hq : q ≠ 1) :
    cap lam S q-cap lam S p = (q-p)*(lam/2-lam*S/((1-p)*(1-q))) := by
  have hp' : 1-p ≠ 0 := sub_ne_zero.mpr hp.symm
  have hq' : 1-q ≠ 0 := sub_ne_zero.mpr hq.symm
  unfold cap
  field_simp
  ring

/-- The known cap bound at xHi continues across the short flat-slack segment. -/
theorem secondExtended_cap (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {r : ℝ} (hr : r ∈ Icc ell tEnd) :
    secondExtendedPrimitive lam phi r ≤ cap lam (finalScalar lam phi) r := by
  have hr0 : (0.28 : ℝ) ≤ r := by convert! hr.1 using 1 <;> norm_num [ell]
  have hr1 : r ≤ (0.385 : ℝ) := by convert! hr.2 using 1 <;> norm_num [tEnd]
  by_cases hrl : r ≤ 0.38
  · rw [secondExtended_eq lam phi ⟨by linarith,by linarith⟩]
    exact second_cap_before_flat h hL hLP ⟨by linarith,hrl⟩
  have hxr : xHi ≤ r := by norm_num [xHi]; linarith
  have hbase := second_cap_before_flat h hL hLP (p := 0.38) (by norm_num)
  rw [secondPrimitive_middle h hL hLP (r := 0.38) (by norm_num)] at hbase
  change quadratic lam (0.38 : ℝ)-finalScalar lam phi ≤ cap lam (finalScalar lam phi) 0.38 at hbase
  rw [secondExtended_middle_formula h hL hLP ⟨hxr,by norm_num [zStart]; linarith⟩]
  have hS := finalScalar_range h hL hLP
  have hS0 : 0 ≤ finalScalar lam phi := by
    have hh := hS.1
    norm_num [Certificates.Compact.scalarLower] at hh
    linarith
  have hS1 : finalScalar lam phi ≤ (0.03 : ℝ) := by
    have hh := hS.2
    norm_num [Certificates.Compact.scalarUpper] at hh
    linarith
  have hL1 : lam ≤ (0.57 : ℝ) := by linarith [hL.2]
  have hden : (0.3 : ℝ) ≤ (1-0.38)*(1-r) := by linarith
  have hden0 : 0 < (1-(0.38 : ℝ))*(1-r) := by linarith
  have hLS := mul_le_mul hL1 hS1 hS0 (by norm_num : (0 : ℝ) ≤ 0.57)
  have hfrac : lam*finalScalar lam phi/((1-0.38)*(1-r)) ≤ (0.06 : ℝ) := by
    apply (div_le_iff₀ hden0).mpr
    nlinarith only [hLS,hden]
  have hcoef : lam-(0.38+r)/2 ≤ lam/2-lam*finalScalar lam phi/((1-0.38)*(1-r)) := by
    linarith
  have hchange := mul_le_mul_of_nonneg_left hcoef (show 0 ≤ r-0.38 by linarith)
  rw [← cap_difference_local lam (finalScalar lam phi) 0.38 r (by norm_num) (by linarith)] at hchange
  have hq : (r-0.38)*(lam-(0.38+r)/2) = quadratic lam r-quadratic lam 0.38 := by
    unfold quadratic
    ring
  rw [hq] at hchange
  linarith

/-- A uniform strict gap between the low cap and the flattened primitive. -/
theorem low_cap_gap (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) :
    cap lam (finalScalar lam phi) 0.36 < quadratic lam 0.38-finalScalar lam phi := by
  have hh := Certificates.Compact.low_average_gt lam (finalScalar lam phi) hL
    (finalScalar_range h hL hLP)
  change (0.09 : ℝ) < (quadratic lam 0.38-finalScalar lam phi-cap lam (finalScalar lam phi) 0.36)/0.02 at hh
  have hn := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 0.02)).mp hh
  nlinarith only [hn]

/-- The complete middle slack budget also covers the short transition before
xHi, where the original primitive need not be monotone. -/
theorem secondExtended_transition_bound (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {r : ℝ} (hr : r ∈ Icc (0.345 : ℝ) 0.38) :
    secondExtendedPrimitive lam phi r ≤ quadratic lam 0.38-finalScalar lam phi+0.00025509854 := by
  have hc := h.central_slack_bound hL hLP
  rw [h.slack_integral (by norm_num) (by norm_num) (by norm_num)] at hc
  rw [←slack_eq lam phi (r := 0.785) (by norm_num),
    ←slack_eq lam phi (r := 0.345) (by norm_num)] at hc
  have hlo := slack_monotone h hr.1
  have hhi := slack_monotone h (by norm_num : (0.38 : ℝ) ≤ 0.785)
  have hdelta : slack lam phi 0.38-slack lam phi r < (0.00025509854 : ℝ) := by linarith
  have hq := quadratic_low_monotone (variational_range hL)
    (show r ∈ Icc ell tEnd by norm_num [ell,tEnd]; constructor <;> linarith [hr.1,hr.2])
    (show (0.38 : ℝ) ∈ Icc ell tEnd by norm_num [ell,tEnd]) hr.2
  rw [secondExtended_low_formula h hL hLP ⟨by linarith [hr.1],hr.2⟩,
    extendedPrimitive_eq phi ⟨by linarith [hr.1],by linarith [hr.2]⟩]
  have he := slack_eq lam phi (r := r) ⟨by linarith [hr.1],by linarith [hr.2]⟩
  unfold cumulativeSlack linePrimitive at he
  unfold finalScalar quadratic at hq ⊢
  linarith

/-- Endpoint domination uses the three-region repair, not the incorrect
backward comparison in the manuscript. -/
theorem secondExtended_endpoint_inputs (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) :
    secondExtendedPrimitive lam phi tEnd = quadratic lam tEnd-finalScalar lam phi ∧
    cap lam (finalScalar lam phi) ell ≤ secondExtendedPrimitive lam phi tEnd ∧
    ∀ r ∈ Icc ell tEnd, secondExtendedPrimitive lam phi r ≤ secondExtendedPrimitive lam phi tEnd := by
  have hl := variational_range hL
  have hSu := finalScalar_admissible_upper h hL hLP
  have hcm := cap_low_monotone hl hSu
  have hqm := quadratic_low_monotone hl
  have hend := secondExtended_middle_formula h hL hLP (r := tEnd) (by norm_num [xHi,tEnd,zStart])
  have hgap := low_cap_gap h hL hLP
  have hQgap : quadratic lam 0.38+(0.00025509854 : ℝ)<quadratic lam tEnd := by
    unfold quadratic
    norm_num [tEnd]
    nlinarith [hL.1]
  have hfloor : cap lam (finalScalar lam phi) ell ≤ secondExtendedPrimitive lam phi tEnd := by
    have hcm' := hcm (show ell ∈ Icc ell tEnd by norm_num [ell,tEnd])
      (show (0.36 : ℝ) ∈ Icc ell tEnd by norm_num [ell,tEnd]) (by norm_num [ell])
    rw [hend]
    linarith
  refine ⟨hend,hfloor,?_⟩
  apply ManuscriptCorrections.endpoint_domination_of_three_regions
    (secondExtendedPrimitive lam phi) (quadratic lam) ell 0.345 0.38 tEnd
    (finalScalar lam phi) (cap lam (finalScalar lam phi) 0.36) 0.00025509854
    ?_ hgap (fun r hr => secondExtended_transition_bound h hL hLP hr) ?_
    (by norm_num) hQgap hend
  · intro r hr
    have hr' : r ∈ Icc ell tEnd := ⟨hr.1,by norm_num [tEnd]; linarith [hr.2]⟩
    exact (secondExtended_cap h hL hLP hr').trans
      (hcm hr' (by norm_num [ell,tEnd]) (by linarith [hr.2]))
  · intro r hr
    have hrI : r ∈ Icc ell tEnd := ⟨by norm_num [ell]; linarith [hr.1],hr.2⟩
    have hrZ : r ∈ Icc xHi zStart := by
      have hrt := hr.2
      norm_num [tEnd] at hrt
      norm_num [xHi,zStart]
      constructor <;> linarith [hr.1]
    rw [secondExtended_middle_formula h hL hLP hrZ]
    exact sub_le_sub_right (hqm hrI (by norm_num [ell,tEnd]) hr.2) _

noncomputable def recoveredEnvelope (lam : ℝ) (phi : ℝ → ℝ) : ℝ → ℝ :=
  runningEnvelope (secondExtendedPrimitive lam phi) ell (cap lam (finalScalar lam phi) ell)
noncomputable def recoveredData (lam : ℝ) (phi : ℝ → ℝ) : LowRankData :=
  ⟨finalScalar lam phi,deriv (recoveredEnvelope lam phi)⟩

theorem recoveredData_admissible (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) :
    Admissible lam (recoveredData lam phi) ∧
      (∀ r ∈ Icc ell tEnd, lowPrimitive lam (recoveredData lam phi) r = recoveredEnvelope lam phi r) ∧
      ∀ r ∈ Icc ell tEnd, secondExtendedPrimitive lam phi r ≤ recoveredEnvelope lam phi r := by
  obtain ⟨K,hK⟩ := secondExtended_lipschitz h
  obtain ⟨hend,hfloor,hdom⟩ := secondExtended_endpoint_inputs h hL hLP
  exact admissible_runningEnvelope (variational_range hL) (finalScalar_admissible_upper h hL hLP)
    hK.continuous.continuousOn (fun _ hx _ hy hxy => secondExtended_increment h hL hLP hx hy hxy)
    (fun _ hr => secondExtended_cap h hL hLP hr) hend hfloor hdom

theorem secondExtended_hasDerivAt (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {r : ℝ} (hr : r ∈ Ioo ell xHi) :
    HasDerivAt (secondExtendedPrimitive lam phi) (phi r) r := by
  have hr0 : (0.245 : ℝ) < r := by have hh := hr.1; norm_num [ell] at hh; linarith
  have hr1 : r < (0.38 : ℝ) := by convert! hr.2 using 1 <;> norm_num [xHi]
  have hd := (extendedPrimitive_hasDerivAt h.continuous r).add_const (prefixGain lam phi)
  rw [clippedActivation_eq phi r ⟨by linarith,by linarith⟩] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr0 hr1] with s hs
  exact secondExtended_low_formula h hL hLP ⟨hs.1.le,hs.2.le⟩

/-- On precisely the interval used by the controls, the new score either
vanishes or retains the original continuous score. -/
theorem recoveredData_score_selection (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) :
    ∀ᵐ r ∂volume.restrict (Icc ell xHi),
      (recoveredData lam phi).phi r = 0 ∨ (recoveredData lam phi).phi r = phi r := by
  obtain ⟨K,hK⟩ := secondExtended_lipschitz h
  exact runningEnvelope_score_selection hK.continuous.continuousOn
    (fun _ hr => secondExtended_hasDerivAt h hL hLP hr)

/-- The admissible piecewise primitive dominates the concrete relocated one at
all candidate-mass coordinates used by the control field. -/
theorem recoveredData_primitive_dominates (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p : ℝ} (hp : p ∈ Icc pLo pHi) :
    secondExtendedPrimitive lam phi p ≤ primitive lam (recoveredData lam phi) p := by
  have hp0 : (0.25 : ℝ) ≤ p := by convert! hp.1 using 1 <;> norm_num [pLo]
  have hp1 : p ≤ (0.36 : ℝ) := by convert! hp.2 using 1 <;> norm_num [pHi]
  by_cases he : p ≤ ell
  · rw [primitive,if_pos he]
    change secondExtendedPrimitive lam phi p ≤ cap lam (finalScalar lam phi) p
    rw [secondExtended_eq lam phi ⟨by linarith,by linarith⟩]
    exact second_cap_before_flat h hL hLP ⟨hp0,by linarith⟩
  · have hpte : p ≤ tEnd := by norm_num [tEnd]; linarith
    have hpI : p ∈ Icc ell tEnd := ⟨(lt_of_not_ge he).le,hpte⟩
    rw [primitive,if_neg he,if_pos hpte]
    have hh := recoveredData_admissible h hL hLP
    rw [hh.2.1 p hpI]
    exact hh.2.2 p hpI

/-- The terminal low-rank cap constraint is inherited from the actual binary
inequality after both slack-removal phases. -/
theorem recoveredData_terminal_cap (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {q : ℝ} (hq : q ∈ Icc qLo qHi) :
    secondExtendedPrimitive lam phi q ≤ cap lam (recoveredData lam phi).S q := by
  have hq0 : (0.26 : ℝ) ≤ q := by convert! hq.1 using 1 <;> norm_num [qLo]
  have hq1 : q ≤ (0.28 : ℝ) := by convert! hq.2 using 1 <;> norm_num [qHi]
  rw [secondExtended_eq lam phi ⟨by linarith,by linarith⟩]
  exact second_cap_before_flat h hL hLP ⟨by linarith,by linarith⟩

end OptimalG.Relocation
