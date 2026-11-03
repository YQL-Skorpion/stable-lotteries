import OptimalG.Certificates.StaticLowGeometry
import OptimalG.ConcaveIncrements

/-! A normalized explicit curve assembled from the fixed low profile and any
checked high score/primitive. The construction makes no use of a minimizer. -/
namespace OptimalG.Certificates.StaticLow
open Set MeasureTheory

noncomputable def completeScore (high : ℝ→ℝ) : ℝ→ℝ :=
  joinAt 0.2635 (headScore 0.2635 (cap lam slack 0.2635) (capSlope lam slack 0.2635))
    (joinAt lam score high)

noncomputable def completePrimitive (P : ℝ→ℝ) : ℝ→ℝ :=
  joinAt 0.2635 (headPrimitive 0.2635 (cap lam slack 0.2635) (capSlope lam slack 0.2635))
    (joinAt lam primitive P)

private theorem low_at_lambda : score lam=0 ∧ primitive lam=quadratic lam lam-slack := by
  have hl : (rightContact:ℝ)≤lam := by norm_num [lam]; linarith only [contacts_real.2.2.2]
  exact ⟨by simpa only [sub_self] using score_line hl,primitive_line hl⟩

private theorem low_strictAnti : StrictAntiOn score (Icc (0.2635:ℝ) lam) := by
  have hhigh : StrictAntiOn score (Icc (0.385:ℝ) lam) := by
    intro r hr s hs hrs
    have hh := (score_post_increment (by linarith only [contacts_real.2.1,hr.1]) hrs.le).2
    linarith only [hh,hrs]
  have hh := strictAntiOn_joinAt (by norm_num : (0.2635:ℝ)≤0.385)
    (by norm_num [lam] : (0.385:ℝ)≤lam) score_strictAnti hhigh rfl
  have he : joinAt (0.385:ℝ) score score=score := by
    funext r
    change (if r≤(0.385:ℝ) then score r else score r)=score r
    split_ifs <;> rfl
  rwa [he] at hh

private theorem low_ceiling {r : ℝ} (hr : r∈Icc (0.2635:ℝ) lam) :
    score r≤(lam:ℝ)-r := by
  by_cases hh : r≤(0.385:ℝ)
  · exact (score_positive_ceiling ⟨hr.1,hh⟩).2
  · exact (score_line (by linarith only [contacts_real.2.2.2,le_of_not_ge hh])).le

theorem completeScore_low {high : ℝ→ℝ} {r : ℝ}
    (hr : r∈Icc (0.2635:ℝ) lam) : completeScore high r=score r := by
  have hj : headScore 0.2635 (cap lam slack 0.2635) (capSlope lam slack 0.2635) 0.2635=
      joinAt (lam:ℝ) score high 0.2635 := by
    rw [joinAt_left _ _ (by norm_num [lam]),headScore_at_join _ _ _ (by norm_num),
      score_cap (by linarith only [contacts_real.1])]
  rw [completeScore,joinAt_right _ _ hr.1 hj,joinAt_left _ _ hr.2]

theorem completeScore_high {high : ℝ→ℝ} (hzero : high lam=0) {r : ℝ}
    (hr : (lam:ℝ)≤r) : completeScore high r=high r := by
  have hx : ¬r≤(0.2635:ℝ) := by
    have hL : (0.2635:ℝ)<lam := by norm_num [lam]
    linarith only [hr,hL]
  rw [completeScore,joinAt,if_neg hx]
  exact joinAt_right _ _ hr (low_at_lambda.1.trans hzero.symm)

theorem completeScore_head {high : ℝ→ℝ} {r : ℝ} (hr : r≤(0.2635:ℝ)) :
    completeScore high r=completeScore high 0+affineHeadSlope*r := by
  simp only [completeScore,joinAt_left _ _ hr,joinAt_left _ _ (by norm_num : (0:ℝ)≤0.2635)]
  simp [headScore,affineHeadSlope]

theorem completePrimitive_hasDerivAt {high P : ℝ→ℝ}
    (hder : ∀ r,HasDerivAt P (high r) r) (hzero : high lam=0)
    (hstart : P lam=quadratic lam lam-slack) (r : ℝ) :
    HasDerivAt (completePrimitive P) (completeScore high r) r := by
  have hl (r : ℝ) : HasDerivAt (joinAt (lam:ℝ) primitive P)
      (joinAt (lam:ℝ) score high r) r :=
    hasDerivAt_glue_le lam primitive P score high primitive_hasDerivAt hder
      (low_at_lambda.2.trans hstart.symm) (low_at_lambda.1.trans hzero.symm) r
  have hv : headPrimitive 0.2635 (cap lam slack 0.2635) (capSlope lam slack 0.2635) 0.2635=
      joinAt (lam:ℝ) primitive P 0.2635 := by
    rw [headPrimitive_at_join _ _ _ (by norm_num),joinAt_left _ _ (by norm_num [lam]),
      primitive_cap (by linarith only [contacts_real.1])]
  have hs : headScore 0.2635 (cap lam slack 0.2635) (capSlope lam slack 0.2635) 0.2635=
      joinAt (lam:ℝ) score high 0.2635 := by
    rw [headScore_at_join _ _ _ (by norm_num),joinAt_left _ _ (by norm_num [lam]),
      score_cap (by linarith only [contacts_real.1])]
  exact hasDerivAt_glue_le 0.2635 _ _ _ _ (headPrimitive_hasDerivAt _ _ _) hl hv hs r

theorem completeScore_continuous {high : ℝ→ℝ} (hcont : Continuous high)
    (hzero : high lam=0) : Continuous (completeScore high) := by
  have hmid : Continuous (joinAt (lam:ℝ) score high) := by
    apply continuous_score.if_le hcont continuous_id continuous_const
    intro r hr
    change r=(lam:ℝ) at hr
    rw [hr,low_at_lambda.1,hzero]
  apply (headScore_continuous 0.2635 (cap lam slack 0.2635) (capSlope lam slack 0.2635)).if_le
    hmid continuous_id continuous_const
  intro r hr
  change r=(0.2635:ℝ) at hr
  rw [hr,headScore_at_join _ _ _ (by norm_num),joinAt_left _ _ (by norm_num [lam]),
    score_cap (by linarith only [contacts_real.1])]

theorem completeScore_primitive {high P : ℝ→ℝ}
    (hcont : Continuous high) (hder : ∀ r,HasDerivAt P (high r) r)
    (hzero : high lam=0) (hstart : P lam=quadratic lam lam-slack) (r : ℝ) :
    curvePrimitive (completeScore high) r=completePrimitive P r := by
  rw [curvePrimitive,intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => completePrimitive_hasDerivAt hder hzero hstart t)
    ((completeScore_continuous hcont hzero).intervalIntegrable 0 r)]
  have h0 : completePrimitive P 0=0 := by
    rw [completePrimitive,joinAt_left _ _ (by norm_num : (0:ℝ)≤0.2635)]
    simp [headPrimitive]
  rw [h0,sub_zero]

theorem completeScore_verifierCurve {high P : ℝ→ℝ}
    (hcont : Continuous high) (hder : ∀ r,HasDerivAt P (high r) r)
    (hzero : high lam=0) (hone : high 1= -1)
    (hstart : P lam=quadratic lam lam-slack) (hend : P 1=0)
    (hfall : ∀ r s,(lam:ℝ)≤r → r≤s → s≤1 → high s-high r≤r-s) :
    VerifierCurve (completeScore high) lam := by
  have hL : (lam:ℝ)∈Ioo (0:ℝ) 1 := by norm_num [lam]
  have hxL : (0.2635:ℝ)≤lam := by norm_num [lam]
  have hj := low_at_lambda.1.trans hzero.symm
  have hhighAnti : StrictAntiOn high (Icc (lam:ℝ) 1) := by
    intro r hr s hs hrs
    have hh := hfall r s hr.1 hrs.le hs.2
    linarith only [hh,hrs]
  have hantiMid := strictAntiOn_joinAt hxL hL.2.le low_strictAnti hhighAnti hj
  have hxjoin : headScore 0.2635 (cap lam slack 0.2635) (capSlope lam slack 0.2635) 0.2635=
      joinAt (lam:ℝ) score high 0.2635 := by
    rw [headScore_at_join _ _ _ (by norm_num),joinAt_left _ _ hxL,
      score_cap (by linarith only [contacts_real.1])]
  have hheadAnti := (headScore_strictAnti 0.2635 (cap lam slack 0.2635)
    (capSlope lam slack 0.2635) (by linarith only [head_scalar_bounds.2.1])).strictAntiOn (Icc 0 0.2635)
  refine ⟨hL.1,hL.2,(completeScore_continuous hcont hzero).continuousOn,
    strictAntiOn_joinAt (by norm_num) (by norm_num) hheadAnti hantiMid hxjoin,?_,?_,?_,?_,?_⟩
  · change curvePrimitive (completeScore high) 1=0
    rw [completeScore_primitive hcont hder hzero hstart]
    simp only [completePrimitive,joinAt,if_neg (by norm_num : ¬(1:ℝ)≤0.2635),
      if_neg (not_le_of_gt hL.2),hend]
  · rw [completeScore_high hzero le_rfl,hzero]
  · rw [completeScore_high hzero hL.2.le,hone]
  · intro r hr
    by_cases hrx : r≤(0.2635:ℝ)
    · rw [completeScore,joinAt_left _ _ hrx]
      exact headScore_ceiling 0.2635 (cap lam slack 0.2635) (capSlope lam slack 0.2635) lam
        (by norm_num) head_scalar_bounds.2.2
        (by have hh := low_ceiling (r:=(0.2635:ℝ)) ⟨le_rfl,hxL⟩
            rwa [score_cap (by linarith only [contacts_real.1])] at hh)
        r ⟨hr.1,hrx⟩
    · by_cases hrl : r≤(lam:ℝ)
      · rw [completeScore_low ⟨le_of_not_ge hrx,hrl⟩]
        exact low_ceiling ⟨le_of_not_ge hrx,hrl⟩
      · rw [completeScore_high hzero (le_of_not_ge hrl)]
        have hh := hfall lam r le_rfl (le_of_not_ge hrl) hr.2
        simpa only [hzero,sub_zero] using hh
  · intro r s hr hrs hs
    rw [completeScore_high hzero hr,completeScore_high hzero (hr.trans hrs)]
    exact hfall r s hr hrs hs

theorem completeScore_lowPrimitive {high P : ℝ→ℝ}
    (hcont : Continuous high) (hder : ∀ r,HasDerivAt P (high r) r)
    (hzero : high lam=0) (hstart : P lam=quadratic lam lam-slack)
    {r : ℝ} (hr : r∈Icc (0.2635:ℝ) lam) :
    curvePrimitive (completeScore high) r=primitive r := by
  rw [completeScore_primitive hcont hder hzero hstart]
  have hj : headPrimitive 0.2635 (cap lam slack 0.2635) (capSlope lam slack 0.2635) 0.2635=
      joinAt (lam:ℝ) primitive P 0.2635 := by
    rw [headPrimitive_at_join _ _ _ (by norm_num),joinAt_left _ _ (by norm_num [lam]),
      primitive_cap (by linarith only [contacts_real.1])]
  rw [completePrimitive,joinAt_right _ _ hr.1 hj,joinAt_left _ _ hr.2]

theorem completeScore_concave {high : ℝ→ℝ} (hzero : high lam=0)
    (hc : ConcaveOn ℝ (Icc (lam:ℝ) 1) high) :
    ConcaveOn ℝ (Icc (lam:ℝ) 1) (completeScore high) := by
  apply hc.congr
  intro r hr
  exact (completeScore_high hzero hr.1).symm

theorem completeScore_binaryGeometry {high P : ℝ→ℝ}
    (hcurve : VerifierCurve (completeScore high) lam)
    (hcont : Continuous high) (hder : ∀ r,HasDerivAt P (high r) r)
    (hzero : high lam=0) (hstart : P lam=quadratic lam lam-slack)
    (hline : ∀ r∈Icc (lam:ℝ) 0.775,high r=(lam:ℝ)-r) :
    BinaryCurveGeometry (completeScore high) lam slack affineHeadSlope leftContact := by
  apply completed_binaryGeometry hcurve
    (fun r hr => completeScore_head hr.2)
  · intro r hr
    exact completeScore_low ⟨hr.1,hr.2.trans (by norm_num [lam])⟩
  · intro r hr
    exact completeScore_lowPrimitive hcont hder hzero hstart
      ⟨hr.1,hr.2.trans (by norm_num [lam])⟩
  · intro r hr
    by_cases hrl : r≤(lam:ℝ)
    · rw [completeScore_low ⟨by linarith only [hr.1],hrl⟩]
      exact score_line (by linarith only [contacts_real.2.2.2,hr.1])
    · rw [completeScore_high hzero (le_of_not_ge hrl)]
      exact hline r ⟨le_of_not_ge hrl,hr.2⟩

theorem completeScore_zero_value (high : ℝ→ℝ) :
    completeScore high 0=headInitial 0.2635 (cap lam slack 0.2635) (capSlope lam slack 0.2635) := by
  rw [completeScore,joinAt_left _ _ (by norm_num : (0:ℝ)≤0.2635)]
  simp [headScore]

theorem completeScore_zero_bounds (high : ℝ→ℝ) :
    (0.437:ℝ)<completeScore high 0 ∧ completeScore high 0<(0.438:ℝ) := by
  rw [completeScore_zero_value]
  norm_num [headInitial,cap,capSlope,lam,slack]

end OptimalG.Certificates.StaticLow
