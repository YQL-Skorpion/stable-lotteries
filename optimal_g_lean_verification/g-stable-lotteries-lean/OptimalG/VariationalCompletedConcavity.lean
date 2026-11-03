import OptimalG.VariationalCompletedCurve

/-! Tail concavity uses a chord inequality at the joining contact. This
avoids assuming differentiability of the minimum of the active controls. -/
namespace OptimalG.Variational
open Set

 theorem completedScore_high_concave_of_chords {lam a J f b Y H m : ℝ} {psi : ℝ → ℝ}
    (ha : a ≠ 0) (hal : a ≤ lam) (hlb : lam ≤ b) (hb : b < 1)
    (hajoin : psi a=f) (hbjoin : psi b=H)
    (hpsi : ConcaveOn ℝ (Icc lam b) psi)
    (htwo : tailTwo b Y H ≤ 0) (htail : tailOne b Y H/(1-b) ≤ m)
    (hchord : ∀ r ∈ Ico lam b,m*(b-r) ≤ psi b-psi r) :
    ConcaveOn ℝ (Icc lam 1) (completedScore a J f b Y H psi) := by
  have htailD : HasDerivWithinAt (tailScore b Y H) (tailOne b Y H/(1-b)) (Icc b 1) b := by
    simpa only [tailSlope,tailCoord,sub_self,zero_div,mul_zero,add_zero] using
      (tailScore_hasDerivAt b Y H b).hasDerivWithinAt (s:=Icc b 1)
  have htailConcave := tailScore_concave b Y H hb htwo
  have hjoin : psi b=tailScore b Y H b := by simpa only [tailScore_at_join] using hbjoin
  have hc := concaveOn_joinAt_of_cross_slopes hlb hb.le hpsi htailConcave hjoin (by
    intro u hu v hv
    have hh := htailConcave.slope_le_of_hasDerivWithinAt ⟨le_rfl,hb.le⟩ ⟨hv.1.le,hv.2⟩ hv.1 htailD
    have hl := (le_div_iff₀ (sub_pos.mpr hu.2)).mpr (hchord u hu)
    have hbound := hh.trans (htail.trans hl)
    simpa only [slope,vsub_eq_sub,smul_eq_mul,div_eq_mul_inv,mul_comm] using hbound)
  apply hc.congr
  intro r hr
  exact (joinAt_right _ _ (hal.trans hr.1) (by
    rw [headScore_at_join a J f ha,joinAt_left _ _ (hal.trans hlb),hajoin])).symm

 theorem completedVariationalScore_high_concave {lam a b m : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (ha : 0 < a) (hax : a ≤ xHi) (hb : b ∈ Icc zStart zEnd)
    (hxjoin : low xHi=lam-xHi) (hzjoin : continuationScore lam d Y zStart=lam-zStart)
    (hactive : ∀ r ∈ Icc zStart b,∀ v ∈ controlFeatureSupport d,
      featureH hd r (Y r) v=vectorField lam d r (Y r) →
      vectorField lam d r (Y r) ≠ lam-r →
      1 ≤ featureTheta lam d v+featureAlpha lam d v*v.1.1)
    (hm : m ≤ -1)
    (hchord : ∀ r ∈ Ico zStart b,m*(b-r) ≤ continuationScore lam d Y b-continuationScore lam d Y r)
    (htwo : tailTwo b (Y b) (continuationScore lam d Y b) ≤ 0)
    (htail : tailOne b (Y b) (continuationScore lam d Y b)/(1-b) ≤ m) :
    ConcaveOn ℝ (Icc lam 1) (completedVariationalScore a lam d low Y b) := by
  have hL := hd.1
  have hxl : xHi ≤ lam := by norm_num [lambdaLo,xHi] at hL ⊢; linarith
  have hlz : lam ≤ zStart := by norm_num [lambdaHi,zStart] at hL ⊢; linarith
  have hb1 : b < 1 := hb.2.trans_lt (by norm_num [zEnd])
  have hshape := continuation_score_concave hd hY le_rfl hb.2 hactive
  apply completedScore_high_concave_of_chords ha.ne' (hax.trans hxl) (hlz.trans hb.1) hb1
    (middleScore_low _ _ _ _ hax) (middleScore_high hxjoin hzjoin hb.1)
    (middleScore_high_concave hxl hlz hb.1 hxjoin hzjoin hshape.2) htwo htail
  intro r hr
  rw [middleScore_high hxjoin hzjoin hb.1]
  by_cases hzr : zStart ≤ r
  · rw [middleScore_high hxjoin hzjoin hzr]
    exact hchord r ⟨hzr,hr.2⟩
  · have hrz : r < zStart := lt_of_not_ge hzr
    rw [middleScore_line hxjoin ⟨hxl.trans hr.1,hrz.le⟩]
    have hzchord : m*(b-zStart) ≤ continuationScore lam d Y b-(lam-zStart) := by
      rcases hb.1.eq_or_lt with he | he
      · subst b
        rw [hzjoin]
        simp
      · simpa only [hzjoin] using hchord zStart ⟨le_rfl,he⟩
    have hmul := mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hrz.le)
    nlinarith only [hzchord,hmul]

end OptimalG.Variational
