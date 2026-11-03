import OptimalG.VariationalCapContact
import OptimalG.VariationalMassLipschitz

/-! The last cap contact lies in the tested rank interval, without sharp tube
estimates. This uses the actual saturation result outside that interval. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem Admissible.cap_strict_below_line_increment {lam a b : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (ha : ell ≤ a) (hab : a < b) (hb : b ≤ xLo) :
    cap lam d.S b-cap lam d.S a < quadratic lam b-quadratic lam a := by
  have hl0 : (56:ℝ)/100 ≤ lam := by have hh := hd.1.1; norm_num [lambdaLo] at hh; linarith
  have hS0 : (2:ℝ)/100 ≤ d.S := by have hh := hd.slack_lower; linarith
  have ha0 : 0 ≤ a := by have hh := ha; norm_num [ell] at hh; linarith
  have hb0 : 0 ≤ b := ha0.trans hab.le
  have hb1 : b ≤ 285/1000 := hb
  have ha1 : a ≤ 285/1000 := hab.le.trans hb1
  have hden0 : 0 < (1-a)*(1-b) := mul_pos (by linarith) (by linarith)
  have hden1 : (1-a)*(1-b) ≤ 1 := by
    have hh := mul_le_mul (show 1-a ≤ 1 by linarith) (show 1-b ≤ 1 by linarith)
      (by linarith : 0 ≤ 1-b) (by norm_num : (0:ℝ) ≤ 1)
    simpa using hh
  have hLS := mul_le_mul hl0 hS0 (by norm_num : (0:ℝ) ≤ 2/100) (by linarith : 0 ≤ lam)
  have hfrac : (1:ℝ)/100 ≤ lam*d.S/((1-a)*(1-b)) := by
    apply (le_div_iff₀ hden0).mpr
    nlinarith only [hLS,hden1]
  have hcoef : lam/2-lam*d.S/((1-a)*(1-b)) < lam-(a+b)/2 := by linarith
  rw [cap_difference lam d.S a b (by linarith) (by linarith)]
  have he : quadratic lam b-quadratic lam a = (b-a)*(lam-(a+b)/2) := by unfold quadratic; ring
  rw [he]
  exact mul_lt_mul_of_pos_left hcoef (sub_pos.mpr hab)

theorem Admissible.cap_root_gap_at_test_end {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    (2:ℝ)/1000 < cap lam d.S xHi-quadratic lam xHi+d.S := by
  have hl := hd.1
  have hS := hd.slack_lower
  have hL0 : (562325:ℝ)/1000000 ≤ lam := hl.1
  have hL1 : lam ≤ (562330:ℝ)/1000000 := hl.2
  have h1 := mul_nonneg (sub_nonneg.mpr hL0)
    (show 0 ≤ lam+(562325:ℝ)/1000000-69/100-(21972:ℝ)/1000000/(62/100) by linarith)
  have h2 := mul_nonneg (sub_nonneg.mpr hS)
    (show 0 ≤ 1-lam/(62/100) by norm_num; linarith)
  norm_num [cap,quadratic,xHi] at h1 h2 ⊢
  nlinarith only [h1,h2]

theorem Admissible.cap_above_root_after_test {lam r : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hr : r ∈ Icc xHi tEnd) : quadratic lam r-d.S < cap lam d.S r := by
  have hl0 : 0 ≤ lam := by have hh := hd.1.1; norm_num [lambdaLo] at hh; linarith
  have hl1 : lam ≤ (57:ℝ)/100 := by have hh := hd.1.2; norm_num [lambdaHi] at hh; linarith
  have hS0 : 0 ≤ d.S := by have hh := hd.slack_lower; linarith
  have hS1 : d.S ≤ (3:ℝ)/100 := by have hh := hd.slack_upper; linarith
  have hr0 : (38:ℝ)/100 ≤ r := hr.1
  have hr1 : r ≤ (385:ℝ)/1000 := hr.2
  have hden : (3:ℝ)/10 ≤ (1-xHi)*(1-r) := by norm_num [xHi]; linarith
  have hden0 : 0 < (1-xHi)*(1-r) := by linarith
  have hLS := mul_le_mul hl1 hS1 hS0 (by norm_num : (0:ℝ) ≤ 57/100)
  have hfrac : lam*d.S/((1-xHi)*(1-r)) ≤ (6:ℝ)/100 := by
    apply (div_le_iff₀ hden0).mpr
    nlinarith only [hLS,hden]
  have hcoef : lam-(xHi+r)/2 ≤ lam/2-lam*d.S/((1-xHi)*(1-r)) := by
    norm_num [xHi] at hfrac ⊢
    linarith
  have hchange := mul_le_mul_of_nonneg_left hcoef (sub_nonneg.mpr hr.1)
  rw [← cap_difference lam d.S xHi r (by norm_num [xHi]) (by linarith)] at hchange
  have he : (r-xHi)*(lam-(xHi+r)/2) = quadratic lam r-quadratic lam xHi := by unfold quadratic; ring
  rw [he] at hchange
  linarith [hd.cap_root_gap_at_test_end]

theorem minimizer_last_contact_in_test_interval {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Icc ell tEnd) (hcontact : lowPrimitive lam d c = cap lam d.S c)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c) :
    xLo ≤ c ∧ c < xHi := by
  have hs := minimizer_saturates_outside_test_interval hd hl hmin hpass hc hlast
  have hline {b : ℝ} (hcb : c ≤ b) (hb : b ≤ tEnd)
      (hout : ∀ r ∈ Ioc c b, r ∉ Icc xLo xHi) :
      lowPrimitive lam d b-lowPrimitive lam d c = quadratic lam b-quadratic lam c := by
    rw [hd.lowPrimitive_sub hc ⟨hc.1.trans hcb,hb⟩]
    have heq : d.phi =ᵐ[volume.restrict (Ioc c b)] (fun r => lam-r) := by
      have hsub : Ioc c b ⊆ Icc ell tEnd := Ioc_subset_Icc_self.trans (Icc_subset_Icc hc.1 hb)
      filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae_restrict_of_subset hsub hs] with r hr hh
      exact hh hr.1 (hout r hr)
    have hi := intervalIntegral.integral_congr_ae_restrict (μ := volume) (a := c) (b := b)
      (by simpa only [uIoc_of_le hcb] using heq)
    rw [hi,integral_line]
  constructor
  · by_contra hnot
    have hcx : c < xLo := lt_of_not_ge hnot
    let b := (c+xLo)/2
    have hcb : c < b := by dsimp [b]; linarith
    have hbx : b < xLo := by dsimp [b]; linarith
    have hb : b ∈ Icc ell tEnd := ⟨hc.1.trans hcb.le,hbx.le.trans (by norm_num [xLo,tEnd])⟩
    have hi := hline hcb.le hb.2 (fun r hr hI => by linarith [hr.2,hI.1])
    have hcap := hd.lowPrimitive_le_cap hb
    have hstrict := hd.cap_strict_below_line_increment hc.1 hcb hbx.le
    rw [hcontact] at hi
    linarith
  · by_contra hnot
    have hxc : xHi ≤ c := le_of_not_gt hnot
    have hi := hline hc.2 le_rfl (fun r hr hI => by linarith [hr.1,hI.2])
    rw [hd.2.2.2.2.1,hcontact] at hi
    have hgap := hd.cap_above_root_after_test ⟨hxc,hc.2⟩
    linarith

end OptimalG.Variational
