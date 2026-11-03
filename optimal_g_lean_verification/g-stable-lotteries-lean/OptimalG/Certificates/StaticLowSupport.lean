import OptimalG.Certificates.StaticLowShape

/-! Global supporting lines for the fixed retargeted low score. -/
namespace OptimalG.Certificates.StaticLow
open Set

noncomputable def slope (r : ℝ) : ℝ :=
  if r≤(rightContact:ℝ) then (scale:ℝ)*UpperTrial.slope r+tilt else -1

private theorem central_slope_bounds {r : ℝ} (hr : (leftContact:ℝ)≤r) :
    -1≤(scale:ℝ)*UpperTrial.slope r+tilt ∧
      (scale:ℝ)*UpperTrial.slope r+tilt≤-(0.691:ℝ) := by
  have hb := UpperTrial.slope_bounds hr
  have hp : UpperProfileData.piece0.slope 0≤-(7/10:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr UpperProfileData.contacts.2.2.2.2
    norm_num [CubicPiece.slope] at hh ⊢
    exact hh.le
  have hk : (0:ℝ)≤scale := by exact_mod_cast retarget_bounds.1.le
  have h1 := mul_le_mul_of_nonneg_left hb.1 hk
  have h2 := mul_le_mul_of_nonneg_left (hb.2.1.trans hp) hk
  have hl : -(1:ℝ)≤-(scale:ℝ)+tilt := by exact_mod_cast retarget_bounds.2.1
  have hu := (Rat.cast_le (K:=ℝ)).mpr retarget_bounds.2.2
  norm_num only [Rat.cast_add,Rat.cast_mul,Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat] at hu
  constructor <;> linarith only [h1,h2,hl,hu]

theorem slope_bounds {r : ℝ} (hr : (leftContact:ℝ)≤r) :
    -1≤slope r ∧ slope r≤-(0.691:ℝ) := by
  unfold slope
  split_ifs
  · exact central_slope_bounds hr
  · norm_num

private theorem central_support {r q : ℝ} (hr : (leftContact:ℝ)≤r)
    (hq : (leftContact:ℝ)≤q) :
    centralScore q≤centralScore r+((scale:ℝ)*UpperTrial.slope r+tilt)*(q-r) := by
  have hh := UpperTrial.supporting_line hr
    (by linarith only [contacts_real.1,hq] : (0.28:ℝ)≤q)
  have hk : (0:ℝ)≤scale := by exact_mod_cast retarget_bounds.1.le
  have hm := mul_le_mul_of_nonneg_left hh hk
  unfold centralScore
  nlinarith only [hm]

private theorem score_le_central {q : ℝ} (hq : (leftContact:ℝ)≤q) :
    score q≤centralScore q := by
  by_cases hqr : q≤(rightContact:ℝ)
  · exact (score_central ⟨hq,hqr⟩).le
  · have hrq := le_of_not_ge hqr
    rw [score_line hrq]
    have hh := (central_increment contacts_real.2.2.1.le hrq).1
    rw [central_end_values.1] at hh
    linarith only [hh]

private theorem post_ceiling {q : ℝ} (hq : (leftContact:ℝ)≤q) : score q≤(lam:ℝ)-q := by
  by_cases hqr : q≤(rightContact:ℝ)
  · have hh := (score_post_increment hq hqr).1
    rw [score_line le_rfl] at hh
    linarith only [hh]
  · exact (score_line (le_of_not_ge hqr)).le

private theorem post_support {r q : ℝ} (hr : (leftContact:ℝ)≤r)
    (hq : (leftContact:ℝ)≤q) : score q≤score r+slope r*(q-r) := by
  by_cases hrr : r≤(rightContact:ℝ)
  · rw [score_central ⟨hr,hrr⟩,slope,if_pos hrr]
    exact (score_le_central hq).trans (central_support hr hq)
  · rw [score_line (le_of_not_ge hrr),slope,if_neg hrr]
    have hh := post_ceiling hq
    linarith only [hh]

theorem supporting_line {r q : ℝ} (hr : (leftContact:ℝ)≤r) (hq : (0.28:ℝ)≤q) :
    score q≤score r+slope r*(q-r) := by
  by_cases hcq : (leftContact:ℝ)≤q
  · exact post_support hr hcq
  · have hqc := le_of_not_ge hcq
    have hp := capSlope_prefix_support (L:=(lam:ℝ)) (S:=(slack:ℝ)) (c:=(leftContact:ℝ))
      (by norm_num [lam]) (by norm_num [slack])
      ⟨by change (0.28:ℝ)≤UpperProfileData.leftContact; linarith only [UpperTrial.contact_range.1],
        by change (UpperProfileData.leftContact:ℝ)≤0.296; exact UpperTrial.contact_range.2.le⟩
      ⟨hq,hqc⟩ (show slope r≤-(0.1:ℝ) by linarith only [(slope_bounds hr).2])
    have hc := post_support hr (q:=(leftContact:ℝ)) le_rfl
    rw [score_cap le_rfl] at hc
    rw [score_cap hqc]
    nlinarith only [hp,hc]

theorem slope_antitone : AntitoneOn slope (Ici (leftContact:ℝ)) := by
  intro r hr s hs hrs
  change (leftContact:ℝ)≤r at hr
  change (leftContact:ℝ)≤s at hs
  rcases hrs.eq_or_lt with he|hlt
  · rw [he]
  · have h1 := supporting_line hr
      (by linarith only [contacts_real.1,hs] : (0.28:ℝ)≤s)
    have h2 := supporting_line hs
      (by linarith only [contacts_real.1,hr] : (0.28:ℝ)≤r)
    have hm : 0≤(slope r-slope s)*(s-r) := by nlinarith only [h1,h2]
    have hh := (mul_nonneg_iff_of_pos_right (sub_pos.mpr hlt)).mp hm
    linarith only [hh]

theorem supporting_line_max {a p y : ℝ} (ha : (leftContact:ℝ)≤a)
    (hy : (0.28:ℝ)≤y) (hyp : p≤y) :
    score y+slope a*(-y)≤score (max a p)+slope a*(-max a p) := by
  by_cases hp : p≤a
  · rw [max_eq_left hp]
    have hs := supporting_line ha hy
    nlinarith only [hs]
  · have hap := le_of_not_ge hp
    rw [max_eq_right hap]
    have hs := supporting_line (ha.trans hap) hy
    have hm := slope_antitone ha (ha.trans hap) hap
    have hm' := mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hyp)
    nlinarith only [hs,hm']

theorem contact_support {d q : ℝ}
    (hdlo : slope leftContact≤d) (hdhi : d≤-(0.1:ℝ)) (hq : (0.28:ℝ)≤q) :
    score q≤score leftContact+d*(q-leftContact) := by
  by_cases hcq : (leftContact:ℝ)≤q
  · have hs := supporting_line (r:=(leftContact:ℝ)) le_rfl hq
    have hm := mul_le_mul_of_nonneg_right hdlo (sub_nonneg.mpr hcq)
    linarith only [hs,hm]
  · have hqc := le_of_not_ge hcq
    have hp := capSlope_prefix_support (L:=(lam:ℝ)) (S:=(slack:ℝ)) (c:=(leftContact:ℝ))
      (by norm_num [lam]) (by norm_num [slack])
      ⟨by change (0.28:ℝ)≤UpperProfileData.leftContact; linarith only [UpperTrial.contact_range.1],
        by change (UpperProfileData.leftContact:ℝ)≤0.296; exact UpperTrial.contact_range.2.le⟩
      ⟨hq,hqc⟩ hdhi
    simpa only [score_cap hqc,score_cap le_rfl] using hp

theorem contact_support_max {d p y : ℝ}
    (hdlo : slope leftContact≤d) (hdhi : d≤-(0.1:ℝ))
    (hy : (0.28:ℝ)≤y) (hyp : p≤y) :
    score y-d*y≤score (max (leftContact:ℝ) p)-d*max (leftContact:ℝ) p := by
  by_cases hp : p≤leftContact
  · rw [max_eq_left hp]
    have hs := contact_support hdlo hdhi hy
    nlinarith only [hs]
  · have hcp := le_of_not_ge hp
    rw [max_eq_right hcp]
    have hs := supporting_line hcp hy
    have hm := (slope_antitone (by simp : (leftContact:ℝ)∈Ici (leftContact:ℝ)) hcp hcp).trans hdlo
    have hm' := mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hyp)
    nlinarith only [hs,hm']

end OptimalG.Certificates.StaticLow
