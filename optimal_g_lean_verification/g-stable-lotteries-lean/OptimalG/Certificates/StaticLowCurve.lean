import OptimalG.Certificates.StaticLowRetarget

/-! The explicit low primitive and score for the static certificate: new cap,
the affine retarget of the accepted cubic chain, and the exact new line. -/
namespace OptimalG.Certificates.StaticLow
open Set

noncomputable def middleScore (r : ℝ) : ℝ :=
  if r≤(rightContact:ℝ) then centralScore r else (lam:ℝ)-r
noncomputable def middlePrimitive (r : ℝ) : ℝ :=
  if r≤(rightContact:ℝ) then centralPrimitive r else quadratic lam r-slack
noncomputable def score (r : ℝ) : ℝ :=
  if r≤(leftContact:ℝ) then capSlope lam slack r else middleScore r
noncomputable def primitive (r : ℝ) : ℝ :=
  if r≤(leftContact:ℝ) then cap lam slack r else middlePrimitive r

theorem contacts_real :
    (0.2918:ℝ)<leftContact ∧ (leftContact:ℝ)<0.305 ∧
      (leftContact:ℝ)<rightContact ∧ (rightContact:ℝ)<0.35945 := by
  norm_num [leftContact,rightContact,UpperProfileData.leftContact,UpperProfileData.rightContact]

theorem middleScore_continuous : Continuous middleScore := by
  apply centralScore_continuous.if_le (continuous_const.sub continuous_id)
    continuous_id continuous_const
  intro r hr
  change r=(rightContact:ℝ) at hr
  change centralScore r=(lam:ℝ)-r
  rw [hr]
  exact central_end_values.1

theorem middlePrimitive_hasDerivAt (r : ℝ) :
    HasDerivAt middlePrimitive (middleScore r) r := by
  apply hasDerivAt_glue_le rightContact centralPrimitive
    (fun t => quadratic lam t-slack) centralScore (fun t => (lam:ℝ)-t)
    centralPrimitive_hasDerivAt ?_ central_end_values.2 central_end_values.1 r
  intro t
  have hh := (((hasDerivAt_id t).const_mul (lam:ℝ)).sub
    (((hasDerivAt_id t).pow 2).div_const 2)).sub_const (slack:ℝ)
  convert! hh using 1 <;> simp [quadratic] <;> ring

theorem middle_start_values :
    middleScore leftContact=capSlope lam slack leftContact ∧
      middlePrimitive leftContact=cap lam slack leftContact := by
  simpa only [middleScore,middlePrimitive,if_pos contacts_real.2.2.1.le] using central_start_values

theorem continuous_score : Continuous score := by
  have hc : (leftContact:ℝ)<1 := by linarith only [contacts_real.2.1]
  have hmin : Continuous (fun r:ℝ => min r (leftContact:ℝ)) :=
    continuous_id.min continuous_const
  have hn : ∀ r:ℝ,(1-min r (leftContact:ℝ))^2≠0 := fun r =>
    pow_ne_zero _ (ne_of_gt (sub_pos.mpr ((min_le_right r _).trans_lt hc)))
  have hp : Continuous (fun r:ℝ => capSlope lam slack (min r leftContact)) := by
    unfold capSlope
    exact continuous_const.sub (continuous_const.div ((continuous_const.sub hmin).pow 2) hn)
  have hh := hp.if_le middleScore_continuous continuous_id continuous_const (by
    intro r hr
    change r=(leftContact:ℝ) at hr
    subst r
    simpa only [min_self] using middle_start_values.1.symm)
  convert hh using 1
  funext r
  by_cases hr : r≤(leftContact:ℝ)
  · simp only [score,id_eq,if_pos hr,min_eq_left hr]
  · simp only [score,id_eq,if_neg hr]

theorem primitive_hasDerivAt (r : ℝ) : HasDerivAt primitive (score r) r := by
  apply hasDerivAt_glue_le_of_left leftContact (cap lam slack) middlePrimitive
    (capSlope lam slack) middleScore ?_ middlePrimitive_hasDerivAt
    middle_start_values.2.symm middle_start_values.1.symm r
  intro t ht
  exact cap_hasDerivAt lam slack t
    (by linarith only [ht,contacts_real.2.1])

theorem score_cap {r : ℝ} (hr : r≤(leftContact:ℝ)) :
    score r=capSlope lam slack r := if_pos hr
theorem primitive_cap {r : ℝ} (hr : r≤(leftContact:ℝ)) :
    primitive r=cap lam slack r := if_pos hr

theorem score_central {r : ℝ} (hr : r∈Icc (leftContact:ℝ) rightContact) :
    score r=centralScore r := by
  rcases eq_or_lt_of_le hr.1 with he|he
  · rw [←he,score_cap le_rfl,central_start_values.1]
  · simp only [score,middleScore,if_neg (not_le_of_gt he),if_pos hr.2]

theorem primitive_central {r : ℝ} (hr : r∈Icc (leftContact:ℝ) rightContact) :
    primitive r=centralPrimitive r := by
  rcases eq_or_lt_of_le hr.1 with he|he
  · rw [←he,primitive_cap le_rfl,central_start_values.2]
  · simp only [primitive,middlePrimitive,if_neg (not_le_of_gt he),if_pos hr.2]

theorem score_line {r : ℝ} (hr : (rightContact:ℝ)≤r) : score r=(lam:ℝ)-r := by
  have hcr := contacts_real.2.2.1.trans_le hr
  rw [score,if_neg (not_le_of_gt hcr),middleScore]
  rcases eq_or_lt_of_le hr with he|he
  · rw [←he,if_pos le_rfl,central_end_values.1]
  · exact if_neg (not_le_of_gt he)

theorem primitive_line {r : ℝ} (hr : (rightContact:ℝ)≤r) :
    primitive r=quadratic lam r-slack := by
  have hcr := contacts_real.2.2.1.trans_le hr
  rw [primitive,if_neg (not_le_of_gt hcr),middlePrimitive]
  rcases eq_or_lt_of_le hr with he|he
  · rw [←he,if_pos le_rfl,central_end_values.2]
  · exact if_neg (not_le_of_gt he)

theorem score_post_increment {r s : ℝ} (hr : (leftContact:ℝ)≤r) (hrs : r≤s) :
    -(s-r)≤score s-score r ∧ score s-score r≤-(691/1000:ℝ)*(s-r) := by
  by_cases hs : s≤(rightContact:ℝ)
  · rw [score_central ⟨hr,hrs.trans hs⟩,score_central ⟨hr.trans hrs,hs⟩]
    exact central_increment hr hrs
  · by_cases hrr : (rightContact:ℝ)≤r
    · rw [score_line hrr,score_line (hrr.trans hrs)]
      constructor <;> linarith only [hrs]
    · have hrx : r≤(rightContact:ℝ) := le_of_not_ge hrr
      have hxs : (rightContact:ℝ)≤s := le_of_not_ge hs
      have hh := central_increment hr hrx
      rw [central_end_values.1] at hh
      rw [score_central ⟨hr,hrx⟩,score_line hxs]
      constructor <;> linarith only [hh.1,hh.2,hxs]

end OptimalG.Certificates.StaticLow
