import OptimalG.Certificates.StaticLowCurve

/-! Pointwise constraints for the explicit low curve, derived from its exact
finite slope bounds and cap joins. These are sufficient constraints, not
properties inferred from an optimizing curve. -/
namespace OptimalG.Certificates.StaticLow
open Set MeasureTheory

theorem cap_derivative_lower {r : ℝ} (hr : r≤(0.385:ℝ)) :
    -(0.126:ℝ)≤-2*(lam:ℝ)*slack/(1-r)^3 := by
  have hp : (0.615:ℝ)^3≤(1-r)^3 := pow_le_pow_left₀ (by norm_num)
    (by linarith only [hr]) 3
  apply (le_div_iff₀ (pow_pos (by linarith only [hr] : 0<1-r) 3)).mpr
  have hn : 2*(lam:ℝ)*slack≤(0.027:ℝ) := by norm_num [lam,slack]
  nlinarith only [hp,hn]

theorem cap_lower_increment {r s : ℝ} (hrs : r≤s) (hs : s≤(0.385:ℝ)) :
    -(0.126:ℝ)*(s-r)≤capSlope lam slack s-capSlope lam slack r := by
  have hd (t : ℝ) (ht : t∈Icc r s) :
      HasDerivAt (fun u => capSlope lam slack u+(0.126:ℝ)*u)
        (-2*(lam:ℝ)*slack/(1-t)^3+0.126) t := by
    convert! (capSlope_hasDerivAt lam slack t (by linarith only [ht.2,hs])).add
      ((hasDerivAt_id t).const_mul (0.126:ℝ)) using 1 <;> ring
  have hm : MonotoneOn (fun u => capSlope lam slack u+(0.126:ℝ)*u) (Icc r s) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    linarith only [cap_derivative_lower ((interior_subset ht).2.trans hs)]
  have hh := hm ⟨le_rfl,hrs⟩ ⟨hrs,le_rfl⟩ hrs
  dsimp only at hh
  linarith only [hh]

theorem cap_antitone : AntitoneOn (capSlope (lam:ℝ) slack) (Iic (0.385:ℝ)) := by
  intro r hr s hs hrs
  change r≤(0.385:ℝ) at hr
  change s≤(0.385:ℝ) at hs
  have hn : (0:ℝ)≤(lam:ℝ)*slack := by norm_num [lam,slack]
  have hds : (0:ℝ)<(1-s)^2 := sq_pos_of_pos (by linarith only [hs])
  have hsq : (1-s)^2≤(1-r)^2 := by nlinarith only [hrs,hs]
  have hh := div_le_div_of_nonneg_left hn hds hsq
  unfold capSlope
  linarith only [hh]

theorem score_le_cap {r : ℝ} (hr : r≤(0.385:ℝ)) : score r≤capSlope lam slack r := by
  by_cases hc : r≤(leftContact:ℝ)
  · exact (score_cap hc).le
  · have hcr := le_of_not_ge hc
    have hl := cap_lower_increment hcr hr
    have hs := (score_post_increment (r:=(leftContact:ℝ)) le_rfl hcr).2
    rw [score_cap le_rfl] at hs
    linarith only [hl,hs,hcr]

theorem score_bounds {r : ℝ} (hr : r∈Icc (0.28:ℝ) 0.385) :
    0≤score r ∧ score r≤(lam:ℝ)-r := by
  have hend : score (0.385:ℝ)=(lam:ℝ)-0.385 :=
    score_line (by linarith only [contacts_real.2.2.2])
  by_cases hc : r≤(leftContact:ℝ)
  · rw [score_cap hc]
    exact capSlope_bounds (by norm_num [lam]) (by norm_num [slack])
      ⟨hr.1,by
        have hh : (leftContact:ℝ)<0.296 := UpperTrial.contact_range.2
        linarith only [hc,hh]⟩
  · have hh := score_post_increment (le_of_not_ge hc) hr.2
    rw [hend] at hh
    constructor
    · have hL : (0.385:ℝ)<lam := by norm_num [lam]
      linarith only [hh.2,hr.2,hL]
    · linarith only [hh.1]

theorem primitive_le_cap {r : ℝ} (hr : r≤(0.385:ℝ)) : primitive r≤cap lam slack r := by
  by_cases hc : r≤(leftContact:ℝ)
  · exact (primitive_cap hc).le
  · have hcr := le_of_not_ge hc
    have hd (t : ℝ) (ht : t∈Icc (leftContact:ℝ) r) :
        HasDerivAt (fun u => cap lam slack u-primitive u) (capSlope lam slack t-score t) t :=
      (cap_hasDerivAt lam slack t (by linarith only [ht.2,hr])).sub (primitive_hasDerivAt t)
    have hm : MonotoneOn (fun u => cap lam slack u-primitive u) (Icc (leftContact:ℝ) r) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
        (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
        (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      intro t ht
      exact sub_nonneg.mpr (score_le_cap ((interior_subset ht).2.trans hr))
    have hh := hm ⟨le_rfl,hcr⟩ ⟨hcr,le_rfl⟩ hcr
    dsimp only at hh
    rw [primitive_cap le_rfl] at hh
    linarith only [hh]

theorem primitive_integral (r : ℝ) :
    cap lam slack 0.28+(∫ t in (0.28:ℝ)..r,score t)=primitive r := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => primitive_hasDerivAt t) (continuous_score.intervalIntegrable 0.28 r),
    primitive_cap (by linarith only [contacts_real.1] : (0.28:ℝ)≤leftContact)]
  ring

end OptimalG.Certificates.StaticLow
