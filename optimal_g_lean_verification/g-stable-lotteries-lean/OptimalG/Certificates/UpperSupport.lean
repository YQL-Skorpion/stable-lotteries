import OptimalG.Certificates.UpperTrial
import OptimalG.Certificates.CubicSupport
import OptimalG.Certificates.CapSupport
import OptimalG.Certificates.RootSupport

/-! Global supporting lines for the exact upper-endpoint trial. -/
namespace OptimalG.Certificates.UpperTrial
open Set UpperProfileData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def slope (r : ℝ) : ℝ := cubicSlope pieces r

private theorem start_before {r : ℝ} (hr : (leftContact:ℝ)≤r) : CubicStartsBefore pieces r := by
  change (piece0.lo:ℝ)≤r
  rwa [endpoint_data.1]

theorem score_eq_cubic {r : ℝ} (hr : (leftContact:ℝ)≤r) :
    score r=cubicScore lam pieces r := by
  by_cases hh : r≤leftContact
  · have he : r=(leftContact:ℝ) := le_antisymm hh hr
    subst r
    simpa only [score,capCubicScore,if_pos le_rfl] using initial_joins.2
  · exact if_neg hh

theorem slope_bounds {r : ℝ} (hr : (leftContact:ℝ)≤r) :
    -1≤slope r ∧ slope r≤piece0.slope 0 ∧ slope r < -(0.1:ℝ) := by
  have hl : pieces=piece0::pieces.tail := rfl
  have hc : cubicAssemblyCheck lam slack (piece0::pieces.tail)=true := by
    simpa only [← hl] using assembly_checked
  have hr' : (piece0.lo:ℝ)≤r := by rwa [endpoint_data.1]
  have hb := cubicAssemblyCheck_slope_bound hc hr'
  have hp := cubicAssemblyCheck_head hc
  have hlen : (0:ℝ)≤piece0.length := by exact_mod_cast le_of_lt (CubicPiece.shapeCheck_length_pos hp)
  have hs := (CubicPiece.shapeCheck_slope hp ⟨le_rfl,hlen⟩).2
  rw [← hl] at hb
  exact ⟨hb.1,hb.2,hb.2.trans_lt hs⟩

/-- Each free-piece or tail slope supports the full score, including the cap
prefix. No sampled-rank assumption occurs in this statement. -/
theorem supporting_line {r q : ℝ} (hr : (leftContact:ℝ)≤r) (hq : (0.28:ℝ)≤q) :
    score q≤score r+slope r*(q-r) := by
  have hrc := score_eq_cubic hr
  by_cases hcq : (leftContact:ℝ)≤q
  · rw [score_eq_cubic hcq,hrc]
    exact cubicAssemblyCheck_support assembly_checked (start_before hr) (start_before hcq)
  · have hqc : q≤(leftContact:ℝ) := le_of_lt (lt_of_not_ge hcq)
    have hcap := capSlope_prefix_support (L:=(lam:ℝ)) (S:=(slack:ℝ))
      (by norm_num [lam]) (by norm_num [slack])
      ⟨by linarith [contact_range.1],le_of_lt contact_range.2⟩ ⟨hq,hqc⟩
      (le_of_lt (slope_bounds hr).2.2)
    have hjoin := initial_joins.2
    have hfree := cubicAssemblyCheck_support assembly_checked (start_before hr)
      (start_before (show (leftContact:ℝ)≤leftContact from le_rfl))
    rw [← hjoin,← hrc] at hfree
    change capSlope lam slack leftContact≤score r+slope r*((leftContact:ℝ)-r) at hfree
    change (if q≤leftContact then capSlope lam slack q else cubicScore lam pieces q)≤_
    rw [if_pos hqc]
    nlinarith only [hcap,hfree]

/-- The assembled slopes are antitone, as follows from the two global
supporting inequalities. -/
theorem slope_antitone : AntitoneOn slope (Ici (leftContact:ℝ)) := by
  intro r hr s hs hrs
  change (leftContact:ℝ)≤r at hr
  change (leftContact:ℝ)≤s at hs
  rcases eq_or_lt_of_le hrs with he | hlt
  · rw [he]
  · have hr0 : (0.28:ℝ)≤r := by linarith [contact_range.1]
    have hs0 : (0.28:ℝ)≤s := hr0.trans hrs
    have h1 := supporting_line hr hs0
    have h2 := supporting_line hs hr0
    have hm : 0≤(slope r-slope s)*(s-r) := by nlinarith only [h1,h2]
    have hh := (mul_nonneg_iff_of_pos_right (sub_pos.mpr hlt)).mp hm
    linarith

/-- The second independent root is constrained below by the layer rank p;
its support point is therefore max(a,p) for the same supporting slope. -/
theorem supporting_line_max {a p y : ℝ} (ha : (leftContact:ℝ)≤a)
    (hy : (0.28:ℝ)≤y) (hyp : p≤y) :
    score y+slope a*(-y)≤score (max a p)+slope a*(-max a p) := by
  by_cases hp : p≤a
  · rw [max_eq_left hp]
    have hs := supporting_line ha hy
    nlinarith only [hs]
  · have hap : a≤p := le_of_lt (lt_of_not_ge hp)
    rw [max_eq_right hap]
    have hs := supporting_line (ha.trans hap) hy
    have hm := slope_antitone ha (ha.trans hap) hap
    have hm' := mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hyp)
    nlinarith only [hs,hm']

/-- At the cap contact every slope between the right slope and the certified
prefix bound is a supporting slope. This handles pinned optimizing roots. -/
theorem contact_support {d q : ℝ}
    (hdlo : slope leftContact≤d) (hdhi : d≤-(0.1:ℝ)) (hq : (0.28:ℝ)≤q) :
    score q≤score leftContact+d*(q-leftContact) := by
  by_cases hcq : (leftContact:ℝ)≤q
  · have hs := supporting_line (r:=(leftContact:ℝ)) le_rfl hq
    have hm := mul_le_mul_of_nonneg_right hdlo (sub_nonneg.mpr hcq)
    linarith
  · have hqc : q≤(leftContact:ℝ) := le_of_lt (lt_of_not_ge hcq)
    have hp := capSlope_prefix_support (L:=(lam:ℝ)) (S:=(slack:ℝ))
      (by norm_num [lam]) (by norm_num [slack])
      ⟨by linarith [contact_range.1],le_of_lt contact_range.2⟩ ⟨hq,hqc⟩ hdhi
    simpa only [score,capCubicScore,if_pos hqc,if_pos le_rfl] using hp

theorem contact_support_max {d p y : ℝ}
    (hdlo : slope leftContact≤d) (hdhi : d≤-(0.1:ℝ))
    (hy : (0.28:ℝ)≤y) (hyp : p≤y) :
    score y-d*y≤score (max (leftContact:ℝ) p)-d*max (leftContact:ℝ) p := by
  by_cases hp : p≤leftContact
  · rw [max_eq_left hp]
    have hs := contact_support hdlo hdhi hy
    nlinarith only [hs]
  · have hcp : (leftContact:ℝ)≤p := le_of_lt (lt_of_not_ge hp)
    rw [max_eq_right hcp]
    have hs := supporting_line hcp hy
    have hm := (slope_antitone (by simp : (leftContact:ℝ)∈Ici (leftContact:ℝ)) hcp hcp).trans hdlo
    have hm' := mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hyp)
    nlinarith only [hs,hm']

end OptimalG.Certificates.UpperTrial
