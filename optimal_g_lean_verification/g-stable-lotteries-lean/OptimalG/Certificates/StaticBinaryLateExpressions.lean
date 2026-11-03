import OptimalG.Certificates.StaticBinaryLateScalars

/-! Scalar branches of the fixed late certificate. The endpoints are included;
where an upper envelope jumps, the comparison has the required orientation. -/
namespace OptimalG.Certificates.StaticBinaryLateExpressions
open Set StaticBinaryCentralExpressions

noncomputable def cutoff : ℝ := binaryAreaCutoff L S c (309/1000)
noncomputable def cutoff2 : ℝ := cutoff-Variational.capSlack L S c/(309/1000)
noncomputable def areaHead (r : ℝ) : ℝ :=
  initial*r+StaticBinaryCentralExpressions.slope*r^2/2-Variational.quadratic L r+S
noncomputable def areaCap (r : ℝ) : ℝ := Variational.capDeficit L S r
noncomputable def areaLinear (r : ℝ) : ℝ :=
  Variational.capSlack L S c*(cutoff-r)-(Variational.capSlack L S c)^2/(2*(309/1000))
noncomputable def areaQuadratic (r : ℝ) : ℝ := (309/2000)*(cutoff-r)^2
noncomputable def upperLeft (r : ℝ) : ℝ :=
  87/1000000000+(24/100000)*(348541/1000000-r)+(309/2000)*(348541/1000000-r)^2
noncomputable def upperRight (_ : ℝ) : ℝ := 87/1000000000
noncomputable def scoreHead (r : ℝ) : ℝ := L-r-(initial+StaticBinaryCentralExpressions.slope*r)
noncomputable def scoreCap (r : ℝ) : ℝ := Variational.capSlack L S r
noncomputable def scoreCone (r : ℝ) : ℝ :=
  Variational.capSlack L S c*(cutoff-r)/(Variational.capSlack L S c/(309/1000)+7189/20000-r)
noncomputable def lower (r : ℝ) : ℝ := binaryAreaLower L S initial
  StaticBinaryCentralExpressions.slope (527/2000) c (7189/20000) (309/1000) r
noncomputable def upper (r : ℝ) : ℝ := binaryAreaUpperProfile L S initial
  StaticBinaryCentralExpressions.slope (527/2000) c (309/1000) (348541/1000000)
    (87/1000000000) (24/100000) r
noncomputable def score (r : ℝ) : ℝ := binaryScoreLower L S initial
  StaticBinaryCentralExpressions.slope (527/2000) c (7189/20000) (309/1000) r

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

-- All constants here are exact rationals; no approximation is used in these comparisons.
theorem cutoff_bounds : c<cutoff2 ∧ cutoff2<(337/1000:ℝ) ∧
    (337/1000:ℝ)<cutoff ∧ cutoff<(7189/20000:ℝ) := by
  norm_num [cutoff2,cutoff,binaryAreaCutoff,L,S,c,StaticLow.lam,StaticLow.slack,
    StaticLow.leftContact,UpperProfileData.leftContact,
    Variational.capDeficit,Variational.capSlack,Variational.cap,Variational.capScore,Variational.quadratic]

theorem contact_reference : c<(348541/1000000:ℝ) := by
  norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]

theorem head_join : areaHead (527/2000)=areaCap (527/2000) := by
  norm_num [areaHead,areaCap,StaticBinaryCentralExpressions.initial,StaticBinaryCentralExpressions.slope,
    SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,headSlope,
    Variational.capDeficit,Variational.cap,Variational.capScore,Variational.quadratic]
  <;> ring

theorem linear_join : areaCap c=areaLinear c := by
  unfold areaCap areaLinear cutoff binaryAreaCutoff
  have hs : Variational.capSlack L S c≠0 := by
    norm_num [Variational.capSlack,Variational.capScore,L,S,c,StaticLow.lam,StaticLow.slack,
      StaticLow.leftContact,UpperProfileData.leftContact]
  field_simp
  <;> ring

theorem lower_head {r : ℝ} (hr : r≤527/2000) : lower r=areaHead r := by
  simp only [lower,binaryAreaLower,if_pos hr,areaHead]

theorem lower_cap {r : ℝ} (hr : r∈Icc (527/2000:ℝ) c) : lower r=areaCap r := by
  by_cases hx : r≤527/2000
  · have he : r=527/2000 := le_antisymm hx hr.1
    subst r
    exact (lower_head le_rfl).trans head_join
  · simp only [lower,binaryAreaLower,if_neg hx,if_pos hr.2,areaCap]

theorem lower_linear {r : ℝ} (hr : r∈Icc c cutoff2) : lower r=areaLinear r := by
  by_cases hc : r≤c
  · have he : r=c := le_antisymm hc hr.1
    subst r
    exact (lower_cap ⟨contact_left.le,le_rfl⟩).trans linear_join
  · have hx : ¬r≤527/2000 := not_le.mpr (contact_left.trans_le hr.1)
    have ht : r≤7189/20000 := hr.2.trans (cutoff_bounds.2.1.le.trans (cutoff_bounds.2.2.1.le.trans cutoff_bounds.2.2.2.le))
    have hfirst : 0≤cutoff-r := by linarith only [hr.2,cutoff_bounds.2.1,cutoff_bounds.2.2.1]
    have hsecond : 0≤cutoff-Variational.capSlack L S c/(309/1000)-r := sub_nonneg.mpr hr.2
    unfold lower binaryAreaLower
    rw [if_neg hx,if_neg hc,if_pos ht]
    change (309/1000)/2*((max (cutoff-r) 0)^2-
      (max (cutoff-Variational.capSlack L S c/(309/1000)-r) 0)^2)=areaLinear r
    rw [max_eq_left hfirst,max_eq_left hsecond]
    unfold areaLinear
    ring

theorem lower_quadratic {r : ℝ} (hr : r∈Icc cutoff2 (337/1000)) :
    lower r=areaQuadratic r := by
  have hc : ¬r≤c := not_le.mpr (cutoff_bounds.1.trans_le hr.1)
  have hx : ¬r≤527/2000 := not_le.mpr (contact_left.trans (cutoff_bounds.1.trans_le hr.1))
  have ht : r≤7189/20000 := hr.2.trans (cutoff_bounds.2.2.1.le.trans cutoff_bounds.2.2.2.le)
  have hfirst : 0≤cutoff-r := by linarith only [hr.2,cutoff_bounds.2.2.1]
  have hsecond : cutoff-Variational.capSlack L S c/(309/1000)-r≤0 := sub_nonpos.mpr hr.1
  unfold lower binaryAreaLower
  rw [if_neg hx,if_neg hc,if_pos ht]
  change (309/1000)/2*((max (cutoff-r) 0)^2-
    (max (cutoff-Variational.capSlack L S c/(309/1000)-r) 0)^2)=areaQuadratic r
  rw [max_eq_left hfirst,max_eq_right hsecond]
  unfold areaQuadratic
  ring

theorem upper_head {r : ℝ} (hr : r≤527/2000) : upper r=areaHead r := by
  simp only [upper,binaryAreaUpperProfile,if_pos hr,areaHead]

theorem upper_cap {r : ℝ} (hr : r∈Icc (527/2000:ℝ) c) : upper r=areaCap r := by
  by_cases hx : r≤527/2000
  · have he : r=527/2000 := le_antisymm hx hr.1
    subst r
    exact (upper_head le_rfl).trans head_join
  · simp only [upper,binaryAreaUpperProfile,if_neg hx,if_pos hr.2,areaCap]

theorem upper_left {r : ℝ} (hr : r∈Icc c (348541/1000000)) : upper r≤upperLeft r := by
  by_cases hc : r≤c
  · have he : r=c := le_antisymm hc hr.1
    subst r
    rw [upper_cap ⟨contact_left.le,le_rfl⟩]
    norm_num [areaCap,upperLeft,L,S,c,StaticLow.lam,StaticLow.slack,
      StaticLow.leftContact,UpperProfileData.leftContact,
      Variational.capDeficit,Variational.cap,Variational.quadratic]
  · have hx : ¬r≤527/2000 := not_le.mpr (contact_left.trans_le hr.1)
    unfold upper binaryAreaUpperProfile
    rw [if_neg hx,if_neg hc]
    unfold binaryAreaUpper upperLeft
    rw [max_eq_left (sub_nonneg.mpr hr.2)]
    norm_num

theorem upper_right {r : ℝ} (hr : (348541/1000000:ℝ)≤r) : upper r=upperRight r := by
  have hc : ¬r≤c := not_le.mpr (contact_reference.trans_le hr)
  have hx : ¬r≤527/2000 := not_le.mpr (contact_left.trans (contact_reference.trans_le hr))
  unfold upper binaryAreaUpperProfile
  rw [if_neg hx,if_neg hc]
  simp [binaryAreaUpper,upperRight,max_eq_right (sub_nonpos.mpr hr)]

end OptimalG.Certificates.StaticBinaryLateExpressions
