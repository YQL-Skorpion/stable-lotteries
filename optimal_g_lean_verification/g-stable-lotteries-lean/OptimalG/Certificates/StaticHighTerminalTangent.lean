import OptimalG.Certificates.StaticHighFacts
import OptimalG.Certificates.StaticTerminal
import Mathlib.Analysis.Convex.Deriv

/-! A single exact left-endpoint derivative bound and high-score concavity
supply the terminal parabola throughout the entire pre-contact interval. -/
namespace OptimalG.Certificates.StaticHighData
open Set Filter MeasureTheory
open scoped Topology

private theorem last_prefix_mem : piece158∈pieces := by simp [pieces]

private theorem last_prefix_hi : (piece158.hi:ℝ)=StaticHigh.contact := by
  norm_num [piece158,StaticHigh.contact]

private theorem last_prefix_lo_lt : (piece158.lo:ℝ)<StaticHigh.contact := by
  norm_num [piece158,StaticHigh.contact]

/-- Actual left derivative at the prescribed terminal contact. -/
theorem contact_left_derivative : HasDerivWithinAt score
    (piece158.slope ((StaticHigh.contact:ℝ)-piece158.lo))
    (Iio (StaticHigh.contact:ℝ)) StaticHigh.contact := by
  have hd := (piece158.score_hasDerivAt ((StaticHigh.contact:ℝ)-piece158.lo)).comp
    (StaticHigh.contact:ℝ) ((hasDerivAt_id (StaticHigh.contact:ℝ)).sub_const (piece158.lo:ℝ))
  simp only [mul_one] at hd
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq
  · have hlo : ∀ᶠ r in 𝓝[<] (StaticHigh.contact:ℝ), (piece158.lo:ℝ)<r :=
      (eventually_gt_nhds last_prefix_lo_lt).filter_mono nhdsWithin_le_nhds
    filter_upwards [hlo,self_mem_nhdsWithin] with r hrlo hrhi
    exact (piece_values last_prefix_mem
      ⟨hrlo.le,by rw [last_prefix_hi]; exact hrhi.le⟩).1
  · exact (piece_values last_prefix_mem
      ⟨last_prefix_lo_lt.le,by rw [last_prefix_hi]⟩).1

theorem contact_left_derivative_bound :
    -(189/100:ℝ)≤piece158.slope ((StaticHigh.contact:ℝ)-piece158.lo) := by
  norm_num [piece158,CubicPiece.slope,StaticHigh.contact]

/-- The terminal left tangent bounds the complete concave high score. -/
theorem score_le_terminal_tangent {r : ℝ}
    (hr : r∈Icc (StaticLow.lam:ℝ) StaticHigh.contact) :
    score r≤(StaticHigh.contactScore:ℝ)-(189/100)*(r-StaticHigh.contact) := by
  have hb : (StaticHigh.contact:ℝ)∈Icc (StaticLow.lam:ℝ) 1 := by
    norm_num [StaticLow.lam,StaticHigh.contact]
  have hvalue : score StaticHigh.contact=(StaticHigh.contactScore:ℝ) := by
    simpa only [tailScore_at_join] using (tail_values ⟨le_rfl,hb.2⟩).1
  rcases lt_or_eq_of_le hr.2 with hlt|heq
  · have hs := score_concave.le_slope_of_hasDerivWithinAt_Iio
      ⟨hr.1,hr.2.trans hb.2⟩ hb hlt contact_left_derivative
    rw [slope_def_field] at hs
    have hh : piece158.slope ((StaticHigh.contact:ℝ)-piece158.lo)*
        ((StaticHigh.contact:ℝ)-r)≤score StaticHigh.contact-score r := by
      exact (le_div_iff₀ (sub_pos.mpr hlt)).mp hs
    have hm := mul_le_mul_of_nonneg_right contact_left_derivative_bound
      (sub_nonneg.mpr hr.2)
    rw [hvalue] at hh
    linarith only [hh,hm]
  · subst r
    rw [hvalue]
    simp

private theorem parabola_hasDerivAt (r : ℝ) : HasDerivAt StaticTerminal.parabola
    ((StaticHigh.contactScore:ℝ)-(189/100)*(r-StaticHigh.contact)) r := by
  have hd := ((hasDerivAt_const r (StaticHigh.contactValue:ℝ)).add
    (((hasDerivAt_id r).sub_const (StaticHigh.contact:ℝ)).const_mul
      (StaticHigh.contactScore:ℝ))).sub
    ((((hasDerivAt_id r).sub_const (StaticHigh.contact:ℝ)).pow 2).const_mul (189/200:ℝ))
  exact hd.congr_deriv (by dsimp; ring)

/-- No interval sampling is required for this terminal lower bound. -/
theorem parabola_le_primitive {r : ℝ}
    (hr : r∈Icc (StaticLow.lam:ℝ) StaticHigh.contact) :
    StaticTerminal.parabola r≤primitive r := by
  have hct : Continuous (fun x : ℝ => (StaticHigh.contactScore:ℝ)-
      (189/100)*(x-StaticHigh.contact)) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ:=volume) hr.2
    (score_continuous.intervalIntegrable r StaticHigh.contact)
    (hct.intervalIntegrable r StaticHigh.contact) (by
      intro x hx
      exact score_le_terminal_tangent ⟨hr.1.trans hx.1,hx.2⟩)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _=>primitive_hasDerivAt x)
      (score_continuous.intervalIntegrable r StaticHigh.contact),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _=>parabola_hasDerivAt x)
      (hct.intervalIntegrable r StaticHigh.contact)] at hi
  have hb : (StaticHigh.contact:ℝ)≤1 := by norm_num [StaticHigh.contact]
  have hj : primitive StaticHigh.contact=(StaticHigh.contactValue:ℝ) := by
    simpa only [tailPrimitive_at_join] using (tail_values ⟨le_rfl,hb⟩).2
  have hp : StaticTerminal.parabola StaticHigh.contact=(StaticHigh.contactValue:ℝ) := by
    simp [StaticTerminal.parabola]
  rw [hj,hp] at hi
  linarith only [hi]

/-- Every pre-contact secant has slope at least the final left derivative. -/
theorem score_lower_increment {r s : ℝ} (hr : (StaticLow.lam:ℝ)≤r)
    (hrs : r≤s) (hs : s≤(StaticHigh.contact:ℝ)) :
    -(189/100:ℝ)*(s-r)≤score s-score r := by
  rcases lt_or_eq_of_le hrs with hlt|heq
  · have hb : (StaticHigh.contact:ℝ)∈Icc (StaticLow.lam:ℝ) 1 := by
      norm_num [StaticLow.lam,StaticHigh.contact]
    have hbound : -(189/100:ℝ)≤(score s-score r)/(s-r) := by
      rcases lt_or_eq_of_le hs with hsb|heq
      · have ht := score_concave.le_slope_of_hasDerivWithinAt_Iio
          ⟨hr.trans hrs,hs.trans hb.2⟩ hb hsb contact_left_derivative
        rw [slope_def_field] at ht
        exact contact_left_derivative_bound.trans (ht.trans
          (score_concave.slope_anti_adjacent ⟨hr,hrs.trans (hs.trans hb.2)⟩ hb hlt hsb))
      · subst s
        have ht := score_concave.le_slope_of_hasDerivWithinAt_Iio
          ⟨hr,hrs.trans hb.2⟩ hb hlt contact_left_derivative
        rw [slope_def_field] at ht
        exact contact_left_derivative_bound.trans ht
    exact (le_div_iff₀ (sub_pos.mpr hlt)).mp hbound
  · subst s
    simp

private noncomputable def departureParabola (r : ℝ) : ℝ :=
  quadratic StaticLow.lam StaticHigh.departure-StaticLow.slack+
    ((StaticLow.lam:ℝ)-StaticHigh.departure)*(r-StaticHigh.departure)-
    (189/200:ℝ)*(r-StaticHigh.departure)^2

private theorem departureParabola_hasDerivAt (r : ℝ) :
    HasDerivAt departureParabola
      ((StaticLow.lam:ℝ)-StaticHigh.departure-(189/100)*(r-StaticHigh.departure)) r := by
  have hd := ((hasDerivAt_const r
    (quadratic StaticLow.lam StaticHigh.departure-StaticLow.slack)).add
    (((hasDerivAt_id r).sub_const (StaticHigh.departure:ℝ)).const_mul
      ((StaticLow.lam:ℝ)-StaticHigh.departure))).sub
    ((((hasDerivAt_id r).sub_const (StaticHigh.departure:ℝ)).pow 2).const_mul (189/200:ℝ))
  exact hd.congr_deriv (by dsimp; ring)

/-- The lower tangent-slope estimate integrates to a quadratic deficit bound. -/
theorem deficit_le_departure_square {r : ℝ}
    (hr : r∈Icc (StaticHigh.departure:ℝ) StaticHigh.contact) :
    quadratic StaticLow.lam r-StaticLow.slack-primitive r≤
      (89/200:ℝ)*(r-StaticHigh.departure)^2 := by
  have ha : (StaticLow.lam:ℝ)≤StaticHigh.departure := by
    norm_num [StaticLow.lam,StaticHigh.departure]
  have hv := line_values (r:=(StaticHigh.departure:ℝ)) ⟨ha,le_rfl⟩
  have hc : Continuous (fun x : ℝ=>(StaticLow.lam:ℝ)-StaticHigh.departure-
      (189/100)*(x-StaticHigh.departure)) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ:=volume) hr.1
    (hc.intervalIntegrable StaticHigh.departure r)
    (score_continuous.intervalIntegrable StaticHigh.departure r) (by
      intro x hx
      have hh := score_lower_increment ha hx.1 (hx.2.trans hr.2)
      rw [hv.1] at hh
      linarith only [hh])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _=>departureParabola_hasDerivAt x)
      (hc.intervalIntegrable StaticHigh.departure r),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _=>primitive_hasDerivAt x)
      (score_continuous.intervalIntegrable StaticHigh.departure r),hv.2] at hi
  dsimp only [departureParabola,quadratic] at hi ⊢
  nlinarith only [hi]

/-- The fixed early-deficit bound follows from concavity, without cell checks. -/
theorem early_deficit {r : ℝ}
    (hr : r∈Icc (StaticLow.lam:ℝ) StaticHigh.contact) :
    quadratic StaticLow.lam r-StaticLow.slack-primitive r≤
      (399/500:ℝ)*max (r-391/500) 0 ^2 := by
  by_cases hra : r≤(StaticHigh.departure:ℝ)
  · rw [(line_values ⟨hr.1,hra⟩).2]
    have hh := sq_nonneg (max (r-391/500) 0)
    nlinarith only [hh]
  · have har : (StaticHigh.departure:ℝ)≤r := (lt_of_not_ge hra).le
    have ha : (391/500:ℝ)≤StaticHigh.departure := by norm_num [StaticHigh.departure]
    have hs : (r-StaticHigh.departure)^2≤(r-391/500)^2 := by
      apply (sq_le_sq₀ (sub_nonneg.mpr har) (sub_nonneg.mpr (ha.trans har))).mpr
      linarith only [ha]
    rw [max_eq_left (sub_nonneg.mpr (ha.trans har))]
    have hh := deficit_le_departure_square ⟨har,hr.2⟩
    nlinarith only [hh,hs,sq_nonneg (r-391/500)]

end OptimalG.Certificates.StaticHighData
