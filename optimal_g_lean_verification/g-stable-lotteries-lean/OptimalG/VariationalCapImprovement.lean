import OptimalG.VariationalCapSlope
import OptimalG.VariationalFeatureBounds

/-! Exact integral rank improvement at a cap contact. This replaces the
paper's unformalized sequence of Lebesgue points by a support point selected
from an integral inequality. Only the full compact scalar box is used. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem Admissible.capScore_gt_small {lam r : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hr : r ∈ Icc ell tEnd) : (24:ℝ)/100 < capScore lam d.S r := by
  have hL0 : (562325:ℝ)/1000000 ≤ lam := hd.1.1
  have hL1 : lam ≤ (562330:ℝ)/1000000 := hd.1.2
  have hS0 : 0 ≤ d.S := by linarith [hd.slack_lower]
  have hS1 := hd.slack_upper
  have hr1 : r ≤ (385:ℝ)/1000 := hr.2
  have hden0 : 0 < (1-r)^2 := sq_pos_of_pos (by linarith)
  have hden : (615/1000:ℝ)^2 ≤ (1-r)^2 := pow_le_pow_left₀ (by norm_num) (by linarith) _
  have hLS := mul_le_mul hL1 hS1 hS0 (by norm_num : (0:ℝ) ≤ 562330/1000000)
  have hc0 : 0 ≤ lam/2-24/100 := by linarith
  have hm := mul_le_mul_of_nonneg_left hden hc0
  have hfrac : lam*d.S/(1-r)^2 < lam/2-24/100 := by
    apply (div_lt_iff₀ hden0).mpr
    norm_num at hden hm
    nlinarith only [hLS,hm,hL0]
  unfold capScore
  linarith

theorem Admissible.cap_quadratic_lower {lam r c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hr : r ∈ Icc ell tEnd) (hc : c ∈ Icc ell tEnd) :
    (c-r)*capScore lam d.S r-(13:ℝ)/200*(c-r)^2 ≤ cap lam d.S c-cap lam d.S r := by
  have hL1 : lam ≤ (562330:ℝ)/1000000 := hd.1.2
  have hS0 : 0 ≤ d.S := by linarith [hd.slack_lower]
  have hS1 := hd.slack_upper
  have hr1 : r ≤ (385:ℝ)/1000 := hr.2
  have hc1 : c ≤ (385:ℝ)/1000 := hc.2
  have hr0 : 0 < 1-r := by linarith
  have hc0 : 0 < 1-c := by linarith
  have hden0 : 0 < (1-r)^2*(1-c) := mul_pos (sq_pos_of_pos hr0) hc0
  have hden : (615/1000:ℝ)^2*(615/1000) ≤ (1-r)^2*(1-c) :=
    mul_le_mul (pow_le_pow_left₀ (by norm_num) (by linarith) 2) (by linarith)
      (by norm_num) (sq_nonneg _)
  have hLS := mul_le_mul hL1 hS1 hS0 (by norm_num : (0:ℝ) ≤ 562330/1000000)
  have hfrac : lam*d.S/((1-r)^2*(1-c)) ≤ (13:ℝ)/200 := by
    apply (div_le_iff₀ hden0).mpr
    norm_num at hden
    nlinarith only [hLS,hden]
  have he : cap lam d.S c-cap lam d.S r =
      (c-r)*capScore lam d.S r-lam*d.S/((1-r)^2*(1-c))*(c-r)^2 := by
    unfold cap capScore
    field_simp [hr0.ne',hc0.ne']
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_right hfrac (sq_nonneg (c-r))
  linarith

private theorem integral_affine_score (A theta r c : ℝ) :
    (∫ u in r..c,A+theta*(r-u)) = (c-r)*A-theta*(c-r)^2/2 := by
  have he : (fun u : ℝ => A+theta*(r-u)) = (fun u => (A+theta*r)-theta*u) := by funext u; ring
  have hi : IntervalIntegrable (fun u : ℝ => theta*u) volume r c :=
    (continuous_const.mul continuous_id).intervalIntegrable r c
  rw [he,intervalIntegral.integral_sub intervalIntegrable_const hi,
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id]
  simp only [smul_eq_mul]
  ring

/-- Every changed rank strictly before a genuine contact can be replaced by a
rank to its right with strictly greater affine score, whenever theta>.13. -/
theorem Admissible.exists_affine_improvement_at_contact {lam c r theta : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : c ∈ Icc ell tEnd) (hcx : c ≤ xHi)
    (hcontact : lowPrimitive lam d c = cap lam d.S c)
    (hr : r ∈ Icc xLo xHi) (hrc : r < c) (htheta : (13:ℝ)/100 < theta) :
    ∃ w ∈ rankScoreSupport d.phi, w.1 ∈ Icc r c ∧
      capScore lam d.S r+theta*r < w.2+theta*w.1 := by
  have hr' : r ∈ Icc ell tEnd := ⟨(by norm_num [ell,xLo] : ell ≤ xLo).trans hr.1,
    hr.2.trans (by norm_num [xHi,tEnd])⟩
  have hsub : Icc r c ⊆ Icc ell tEnd := Icc_subset_Icc hr'.1 hc.2
  by_contra hn
  push_neg at hn
  have hb : ∀ᵐ s ∂volume.restrict (Icc r c), d.phi s ≤ capScore lam d.S r+theta*(r-s) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae_restrict_of_subset hsub hd.ae_low_rankScore_mem] with s hs hg
    have hG := hg ⟨hr.1.trans hs.1,hs.2.trans hcx⟩
    have hh := hn (s,d.phi s) hG hs
    dsimp at hh
    nlinarith
  have hi := intervalIntegral.integral_mono_ae_restrict hrc.le
    (hd.intervalIntegrable hr'.1 hrc.le hc.2)
    ((continuous_const.add (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable r c) hb
  change (∫ s in r..c,d.phi s) ≤ ∫ s in r..c,capScore lam d.S r+theta*(r-s) at hi
  rw [integral_affine_score,← hd.lowPrimitive_sub hr' hc,hcontact] at hi
  have hcap := hd.lowPrimitive_le_cap hr'
  have htaylor := hd.cap_quadratic_lower hr' hc
  have hpos := mul_pos (sub_pos.mpr htheta) (sq_pos_of_pos (sub_pos.mpr hrc))
  nlinarith only [hi,hcap,htaylor,hpos]

end OptimalG.Variational
