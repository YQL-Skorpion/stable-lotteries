import OptimalG.Certificates.StaticBinaryLateExpressions

namespace OptimalG.Certificates.StaticBinaryLateExpressions
open Set StaticBinaryCentralExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem score_head {r : ℝ} (hr : r≤527/2000) : score r=scoreHead r := by
  simp only [score,binaryScoreLower,if_pos hr,scoreHead]

theorem score_head_join : scoreHead (527/2000)=scoreCap (527/2000) := by
  norm_num [scoreHead,scoreCap,StaticBinaryCentralExpressions.initial,StaticBinaryCentralExpressions.slope,
    SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,headSlope,
    Variational.capSlack,Variational.cap,Variational.capScore]
  <;> ring

theorem score_cap {r : ℝ} (hr : r∈Icc (527/2000:ℝ) c) : score r=scoreCap r := by
  by_cases hx : r≤527/2000
  · have he : r=527/2000 := le_antisymm hx hr.1
    subst r
    exact (score_head le_rfl).trans score_head_join
  · simp only [score,binaryScoreLower,if_neg hx,if_pos hr.2,scoreCap]

theorem score_cone_le {r : ℝ} (hr : r∈Icc c cutoff) : scoreCone r≤score r := by
  by_cases hc : r≤c
  · have he : r=c := le_antisymm hc hr.1
    subst r
    rw [score_cap ⟨contact_left.le,le_rfl⟩]
    norm_num [scoreCone,scoreCap,cutoff,binaryAreaCutoff,L,S,c,StaticLow.lam,StaticLow.slack,
      StaticLow.leftContact,UpperProfileData.leftContact,
      Variational.capDeficit,Variational.capSlack,Variational.cap,Variational.capScore,Variational.quadratic]
  · have hx : ¬r≤527/2000 := not_le.mpr (contact_left.trans_le hr.1)
    have ht : r≤7189/20000 := hr.2.trans cutoff_bounds.2.2.2.le
    unfold score binaryScoreLower
    rw [if_neg hx,if_neg hc,if_pos ht]
    unfold binaryScoreCone
    change scoreCone r≤Variational.capSlack L S c*max (cutoff-r) 0/
      (Variational.capSlack L S c/(309/1000)+7189/20000-r)
    rw [max_eq_left (sub_nonneg.mpr hr.2)]
    exact le_rfl

theorem score_zero {r : ℝ} (hr : cutoff≤r) : score r=0 := by
  have hc : ¬r≤c := not_le.mpr
    (cutoff_bounds.1.trans (cutoff_bounds.2.1.trans cutoff_bounds.2.2.1) |>.trans_le hr)
  have hx : ¬r≤527/2000 := not_le.mpr (contact_left.trans (not_le.mp hc))
  unfold score binaryScoreLower
  rw [if_neg hx,if_neg hc]
  split_ifs with ht
  · unfold binaryScoreCone
    change Variational.capSlack L S c*max (cutoff-r) 0/_=0
    rw [max_eq_right (sub_nonpos.mpr hr)]
    simp
  · rfl

noncomputable def rightSum (q : ℝ) : ℝ :=
  (50/3)*(score (q+1/150)+score (q+1/75)+score (q+1/50))-B*(L-q)+1/2

theorem rightSum_eq (q : ℝ) :
    2500*(∑ i∈Finset.range 3,(1/(50*(3:ℝ)))*
      binaryScoreLower L S initial StaticBinaryCentralExpressions.slope
        (527/2000) c (7189/20000) (309/1000) (q+((i:ℝ)+1)/(50*(3:ℝ))))-
      B*(L-q)+1/2=rightSum q := by
  norm_num [Finset.sum_range_succ,rightSum,score]
  <;> ring

end OptimalG.Certificates.StaticBinaryLateExpressions
