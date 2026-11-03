import OptimalG.Certificates.StaticCompletion
import OptimalG.Certificates.StaticHighFacts

/-! The frozen explicit normalized score and its actual integral primitive.
This module constructs the curve; the all-mass inequalities are separate checks. -/
namespace OptimalG.Certificates.StaticCurve
open Set

noncomputable def score : ℝ→ℝ := StaticLow.completeScore StaticHighData.score
noncomputable def primitive : ℝ→ℝ := curvePrimitive score

theorem verifierCurve : VerifierCurve score StaticLow.lam :=
  StaticLow.completeScore_verifierCurve StaticHighData.score_continuous
    StaticHighData.primitive_hasDerivAt StaticHighData.initial_score StaticHighData.terminal_score
    StaticHighData.initial_primitive StaticHighData.terminal_primitive
    (fun r s hr hrs hs => by
      have hh := StaticHighData.score_fall hr hrs hs
      linarith only [hh])

theorem concave : ConcaveOn ℝ (Icc (StaticLow.lam:ℝ) 1) score :=
  StaticLow.completeScore_concave StaticHighData.initial_score StaticHighData.score_concave

theorem low_score {r : ℝ} (hr : r∈Icc (0.2635:ℝ) StaticLow.lam) :
    score r=StaticLow.score r := StaticLow.completeScore_low hr

theorem low_primitive {r : ℝ} (hr : r∈Icc (0.2635:ℝ) StaticLow.lam) :
    primitive r=StaticLow.primitive r :=
  StaticLow.completeScore_lowPrimitive StaticHighData.score_continuous
    StaticHighData.primitive_hasDerivAt StaticHighData.initial_score StaticHighData.initial_primitive hr

theorem high_score {r : ℝ} (hr : (StaticLow.lam:ℝ)≤r) :
    score r=StaticHighData.score r := StaticLow.completeScore_high StaticHighData.initial_score hr

theorem high_primitive {r : ℝ} (hr : (StaticLow.lam:ℝ)≤r) :
    primitive r=StaticHighData.primitive r := by
  change curvePrimitive (StaticLow.completeScore StaticHighData.score) r=_
  rw [StaticLow.completeScore_primitive StaticHighData.score_continuous
    StaticHighData.primitive_hasDerivAt StaticHighData.initial_score StaticHighData.initial_primitive]
  have hx : ¬r≤(0.2635:ℝ) := by
    have hL : (0.2635:ℝ)<StaticLow.lam := by norm_num [StaticLow.lam]
    linarith only [hr,hL]
  rw [StaticLow.completePrimitive,joinAt,if_neg hx]
  apply joinAt_right _ _ hr
  rw [StaticLow.primitive_line (by norm_num [StaticLow.lam,StaticLow.rightContact,
    UpperProfileData.rightContact]),StaticHighData.initial_primitive]

theorem line_values {r : ℝ}
    (hr : r∈Icc (StaticLow.rightContact:ℝ) StaticHigh.departure) :
    score r=(StaticLow.lam:ℝ)-r ∧ primitive r=quadratic StaticLow.lam r-StaticLow.slack := by
  by_cases hrl : r≤(StaticLow.lam:ℝ)
  · have hx : (0.2635:ℝ)≤r := by
      have hh := StaticLow.contacts_real
      linarith only [hh.1,hh.2.2.1,hr.1]
    rw [low_score ⟨hx,hrl⟩,low_primitive ⟨hx,hrl⟩]
    exact ⟨StaticLow.score_line hr.1,StaticLow.primitive_line hr.1⟩
  · rw [high_score (le_of_not_ge hrl),high_primitive (le_of_not_ge hrl)]
    exact StaticHighData.line_values ⟨le_of_not_ge hrl,hr.2⟩

theorem head_formula {r : ℝ} (hr : r≤(0.2635:ℝ)) :
    score r=headScore 0.2635 (cap StaticLow.lam StaticLow.slack 0.2635)
      (capSlope StaticLow.lam StaticLow.slack 0.2635) r :=
  joinAt_left _ _ hr

theorem head {r : ℝ} (hr : r≤(0.2635:ℝ)) :
    score r=score 0+StaticLow.affineHeadSlope*r := StaticLow.completeScore_head hr

theorem initial_value : score 0=headInitial 0.2635 (cap StaticLow.lam StaticLow.slack 0.2635)
    (capSlope StaticLow.lam StaticLow.slack 0.2635) := StaticLow.completeScore_zero_value _

theorem initial_bounds : (0.437:ℝ)<score 0 ∧ score 0<(0.438:ℝ) :=
  StaticLow.completeScore_zero_bounds _

theorem binaryGeometry : BinaryCurveGeometry score StaticLow.lam StaticLow.slack
    StaticLow.affineHeadSlope StaticLow.leftContact := by
  apply StaticLow.completeScore_binaryGeometry verifierCurve StaticHighData.score_continuous
    StaticHighData.primitive_hasDerivAt StaticHighData.initial_score StaticHighData.initial_primitive
  intro r hr
  exact (StaticHighData.line_values ⟨hr.1,hr.2.trans
    (by norm_num [StaticHigh.departure])⟩).1

theorem cap_values {r : ℝ} (hr : r∈Icc (0.2635:ℝ) StaticLow.leftContact) :
    score r=capSlope StaticLow.lam StaticLow.slack r ∧
      primitive r=cap StaticLow.lam StaticLow.slack r := by
  have hl : r≤(StaticLow.lam:ℝ) := hr.2.trans (by
    have hh := StaticLow.contacts_real.2.1
    norm_num [StaticLow.lam]
    linarith only [hh])
  rw [low_score ⟨hr.1,hl⟩,low_primitive ⟨hr.1,hl⟩]
  exact ⟨StaticLow.score_cap hr.2,StaticLow.primitive_cap hr.2⟩

theorem tail_values {r : ℝ} (hr : r∈Icc (StaticHigh.contact:ℝ) 1) :
    score r=tailScore StaticHigh.contact StaticHigh.contactValue StaticHigh.contactScore r ∧
      primitive r=tailPrimitive StaticHigh.contact StaticHigh.contactValue StaticHigh.contactScore r := by
  have hl : (StaticLow.lam:ℝ)≤r :=
    (by norm_num [StaticLow.lam,StaticHigh.contact] : (StaticLow.lam:ℝ)≤StaticHigh.contact).trans hr.1
  rw [high_score hl,high_primitive hl]
  exact StaticHighData.tail_values hr

theorem contact_values : score StaticHigh.contact=StaticHigh.contactScore ∧
    primitive StaticHigh.contact=StaticHigh.contactValue := by
  have hh := tail_values (r:=(StaticHigh.contact:ℝ)) ⟨le_rfl,by norm_num [StaticHigh.contact]⟩
  simpa only [tailScore_at_join,tailPrimitive_at_join] using hh

end OptimalG.Certificates.StaticCurve
