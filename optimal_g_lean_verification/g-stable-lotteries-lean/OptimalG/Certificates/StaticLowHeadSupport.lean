import OptimalG.Certificates.StaticLowSupport

/-! The same static supports hold down to the affine-head join, so supporting
controls do not need a variational-domain restriction at rank .28. -/
namespace OptimalG.Certificates.StaticLow
open Set

private theorem cap_prefix_derivative {r : ℝ} (hr : r≤(leftContact:ℝ)) :
    -(0.1:ℝ)≤-2*(lam:ℝ)*slack/(1-r)^3 := by
  have hc : (leftContact:ℝ)<(0.296:ℝ) := UpperTrial.contact_range.2
  have hp : (0.704:ℝ)^3≤(1-r)^3 := pow_le_pow_left₀ (by norm_num)
    (by linarith only [hr,hc]) 3
  have hn : 2*(lam:ℝ)*slack≤(0.027:ℝ) := by norm_num [lam,slack]
  apply (le_div_iff₀ (pow_pos (by linarith only [hr,hc] : 0<1-r) 3)).mpr
  nlinarith only [hp,hn]

private theorem cap_prefix_increment {r s : ℝ} (hrs : r≤s)
    (hs : s≤(leftContact:ℝ)) :
    -(0.1:ℝ)*(s-r)≤capSlope lam slack s-capSlope lam slack r := by
  have hd (t : ℝ) (ht : t∈Icc r s) :
      HasDerivAt (fun u => capSlope lam slack u+(0.1:ℝ)*u)
        (-2*(lam:ℝ)*slack/(1-t)^3+0.1) t := by
    convert! (capSlope_hasDerivAt lam slack t
      (by linarith only [ht.2,hs,contacts_real.2.1])).add
      ((hasDerivAt_id t).const_mul (0.1:ℝ)) using 1 <;> ring
  have hm : MonotoneOn (fun u => capSlope lam slack u+(0.1:ℝ)*u) (Icc r s) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    linarith only [cap_prefix_derivative ((interior_subset ht).2.trans hs)]
  have hh := hm ⟨le_rfl,hrs⟩ ⟨hrs,le_rfl⟩ hrs
  dsimp only at hh
  linarith only [hh]

private theorem cap_prefix_support {q d : ℝ}
    (hq : q≤(leftContact:ℝ)) (hd : d≤-(0.1:ℝ)) :
    capSlope lam slack q≤capSlope lam slack leftContact+d*(q-leftContact) := by
  have hh := cap_prefix_increment hq le_rfl
  have hm := mul_le_mul_of_nonpos_right hd (sub_nonpos.mpr hq)
  nlinarith only [hh,hm]

theorem supporting_line_head {r q : ℝ} (hr : (leftContact:ℝ)≤r)
    (hq : (0.2635:ℝ)≤q) : score q≤score r+slope r*(q-r) := by
  by_cases hqc : (leftContact:ℝ)≤q
  · exact supporting_line hr (by linarith only [contacts_real.1,hqc])
  · have hqc' := le_of_not_ge hqc
    have hp := cap_prefix_support hqc'
      (show slope r≤-(0.1:ℝ) by linarith only [(slope_bounds hr).2])
    have hc := supporting_line hr (q:=(leftContact:ℝ))
      (by linarith only [contacts_real.1])
    rw [score_cap le_rfl] at hc
    rw [score_cap hqc']
    nlinarith only [hp,hc]

theorem supporting_line_max_head {a p y : ℝ} (ha : (leftContact:ℝ)≤a)
    (hy : (0.2635:ℝ)≤y) (hyp : p≤y) :
    score y+slope a*(-y)≤score (max a p)+slope a*(-max a p) := by
  by_cases hp : p≤a
  · rw [max_eq_left hp]
    have hs := supporting_line_head ha hy
    nlinarith only [hs]
  · have hap := le_of_not_ge hp
    rw [max_eq_right hap]
    have hs := supporting_line_head (ha.trans hap) hy
    have hm := slope_antitone ha (ha.trans hap) hap
    have hm' := mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hyp)
    nlinarith only [hs,hm']

theorem contact_support_head {d q : ℝ}
    (hdlo : slope leftContact≤d) (hdhi : d≤-(0.1:ℝ)) (hq : (0.2635:ℝ)≤q) :
    score q≤score leftContact+d*(q-leftContact) := by
  by_cases hcq : (leftContact:ℝ)≤q
  · exact contact_support hdlo hdhi (by linarith only [contacts_real.1,hcq])
  · have hqc := le_of_not_ge hcq
    rw [score_cap hqc,score_cap le_rfl]
    exact cap_prefix_support hqc hdhi

theorem contact_support_max_head {d p y : ℝ}
    (hdlo : slope leftContact≤d) (hdhi : d≤-(0.1:ℝ))
    (hy : (0.2635:ℝ)≤y) (hyp : p≤y) :
    score y-d*y≤score (max (leftContact:ℝ) p)-d*max (leftContact:ℝ) p := by
  by_cases hp : p≤leftContact
  · rw [max_eq_left hp]
    have hs := contact_support_head hdlo hdhi hy
    nlinarith only [hs]
  · have hcp := le_of_not_ge hp
    rw [max_eq_right hcp]
    have hs := supporting_line_head hcp hy
    have hm := (slope_antitone (by simp : (leftContact:ℝ)∈Ici (leftContact:ℝ)) hcp hcp).trans hdlo
    have hm' := mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hyp)
    nlinarith only [hs,hm']

end OptimalG.Certificates.StaticLow
