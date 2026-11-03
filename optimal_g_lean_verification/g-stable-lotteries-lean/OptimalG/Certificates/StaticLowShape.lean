import OptimalG.Certificates.StaticLowBounds
import OptimalG.VariationalLowCurve

/-! The full static low score has the finite shape bounds required by the
election verifier. All shape comes from the fixed polynomial calibration. -/
namespace OptimalG.Certificates.StaticLow
open Set

theorem score_capRegular :
    Variational.capRegularScore lam slack leftContact score=score := by
  funext r
  by_cases hr : r≤(leftContact:ℝ)
  · simp only [Variational.capRegularScore,if_pos hr,score_cap hr]
    rfl
  · exact if_neg hr

theorem cap_join : score leftContact=Variational.capScore lam slack leftContact := by
  exact score_cap le_rfl

theorem score_strictAnti : StrictAntiOn score (Icc (0.2635:ℝ) 0.385) := by
  rw [←score_capRegular]
  apply Variational.capRegularScore_strictAntiOn
    (by linarith only [contacts_real.1]) (by linarith only [contacts_real.2.1])
    (by norm_num) (by norm_num [lam]) (by norm_num [slack]) cap_join
  intro r hr s hs hrs
  have hh := (score_post_increment hr.1 hrs.le).2
  linarith only [hh,hrs]

theorem score_lower_increment :
    ∀ r∈Icc (0.2635:ℝ) 0.385,∀ s∈Icc (0.2635:ℝ) 0.385,r≤s →
      score r-(s-r)≤score s := by
  have hh := Variational.capRegularScore_lower_increment
    (lam:=(lam:ℝ)) (S:=(slack:ℝ)) (c:=(leftContact:ℝ)) (psi:=score)
    (a:=0.2635) (b:=0.385)
    (by linarith only [contacts_real.1]) (by linarith only [contacts_real.2.1])
    (by norm_num) cap_join
    (by
      intro r hr
      have hc := cap_derivative_lower (hr.2.trans (by linarith only [contacts_real.2.1]))
      linarith only [hc])
    (by
      intro r hr s hs hrs
      have h := (score_post_increment hr.1 hrs).1
      linarith only [h])
  simpa only [score_capRegular] using hh

theorem score_lipschitz : LipschitzOnWith 1 score (Icc (0.2635:ℝ) 0.385) :=
  Variational.antitone_lower_increment_lipschitz score_strictAnti.antitoneOn score_lower_increment

theorem score_positive_ceiling {r : ℝ} (hr : r∈Icc (0.2635:ℝ) 0.385) :
    0<score r ∧ score r≤(lam:ℝ)-r := by
  have he := score_line (r:=(0.385:ℝ))
    (by linarith only [contacts_real.2.2.2])
  have ha := score_strictAnti.antitoneOn hr ⟨by norm_num,le_rfl⟩ hr.2
  have hl := score_lower_increment r hr 0.385 ⟨by norm_num,le_rfl⟩ hr.2
  rw [he] at ha hl
  have hL : (0.385:ℝ)<lam := by norm_num [lam]
  constructor <;> linarith only [ha,hl,hL]

theorem head_scalar_bounds :
    -(691/1000:ℝ)<headSlope 0.2635 (cap lam slack 0.2635) (capSlope lam slack 0.2635) ∧
    headSlope 0.2635 (cap lam slack 0.2635) (capSlope lam slack 0.2635) < -(0.126:ℝ) ∧
    headInitial 0.2635 (cap lam slack 0.2635) (capSlope lam slack 0.2635)≤(lam:ℝ) := by
  norm_num [headSlope,headInitial,cap,capSlope,lam,slack]

theorem cap_pre_increment {r s : ℝ} (hr : (0.2635:ℝ)≤r)
    (hrs : r≤s) (hs : s≤(leftContact:ℝ)) :
    headSlope 0.2635 (cap lam slack 0.2635) (capSlope lam slack 0.2635)*(s-r)≤
      score s-score r := by
  rw [score_cap hs,score_cap (hrs.trans hs)]
  have hh := cap_lower_increment hrs (hs.trans (by linarith only [contacts_real.2.1]))
  have hm := mul_le_mul_of_nonneg_right head_scalar_bounds.2.1.le (sub_nonneg.mpr hrs)
  exact hm.trans hh

end OptimalG.Certificates.StaticLow
