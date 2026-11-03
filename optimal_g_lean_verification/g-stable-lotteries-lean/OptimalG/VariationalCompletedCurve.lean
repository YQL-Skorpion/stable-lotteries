import OptimalG.VariationalMiddleCurve
import OptimalG.VariationalRepresentativeGraph

/-! An actual polynomial completion of the recovered minimizing low curve
and its variational continuation. The score graph and primitive identities
link the completed verifier back to the original relaxed data. -/
namespace OptimalG.Variational
open Set MeasureTheory
open scoped NNReal

noncomputable def completedVariationalScore (a lam : ℝ) (d : LowRankData)
    (low Y : ℝ → ℝ) (b : ℝ) : ℝ → ℝ :=
  completedScore a (cap lam d.S a) (low a) b (Y b) (continuationScore lam d Y b)
    (middleScore lam d low Y)

 theorem completedVariationalScore_low {lam a b : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (ha : 0 < a) (hax : a ≤ xHi) (hb : zStart ≤ b)
    {r : ℝ} (hr : r ∈ Icc a xHi) : completedVariationalScore a lam d low Y b r=low r := by
  have hxb : xHi ≤ b := (by norm_num [xHi,zStart] : xHi ≤ zStart).trans hb
  rw [completedVariationalScore,completedScore_middle ha.ne' (hax.trans hxb)
    (middleScore_low _ _ _ _ hax) ⟨hr.1,hr.2.trans hxb⟩,
    middleScore_low _ _ _ _ hr.2]



 theorem completedVariationalScore_line {lam a b z : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (ha : 0 < a) (hax : a ≤ xHi) (hz : z ∈ Icc zStart b)
    (hxjoin : low xHi=lam-xHi)
    (hline : ∀ r ∈ Icc zStart z,continuationScore lam d Y r=lam-r) :
    ∀ r ∈ Icc xHi z,completedVariationalScore a lam d low Y b r=lam-r := by
  have hxz : xHi ≤ zStart := by norm_num [xHi,zStart]
  have hb : zStart ≤ b := hz.1.trans hz.2
  have hzjoin := hline zStart ⟨le_rfl,hz.1⟩
  intro r hr
  rw [completedVariationalScore,completedScore_middle ha.ne' (hax.trans (hxz.trans hb))
    (middleScore_low _ _ _ _ hax) ⟨hax.trans hr.1,hr.2.trans hz.2⟩]
  by_cases hrz : r ≤ zStart
  · exact middleScore_line hxjoin ⟨hr.1,hrz⟩
  · rw [middleScore_high hxjoin hzjoin (le_of_not_ge hrz)]
    exact hline r ⟨le_of_not_ge hrz,hr.2⟩

 theorem completedVariationalScore_cap {lam a b c : ℝ} {d : LowRankData} {psi Y : ℝ → ℝ}
    (ha : 0 < a) (hax : a ≤ xLo) (hcx : xLo ≤ c) (hb : zStart ≤ b) :
    ∀ r ∈ Icc a xLo,
      completedVariationalScore a lam d (capRegularScore lam d.S c psi) Y b r=capScore lam d.S r := by
  intro r hr
  have hxx : xLo ≤ xHi := by norm_num [xLo,xHi]
  rw [completedVariationalScore_low ha (hax.trans hxx) hb ⟨hr.1,hr.2.trans hxx⟩,
    capRegularScore_left _ _ _ _ (hr.2.trans hcx)]

 theorem completedVariationalScore_low_lipschitz {lam a b : ℝ} {d : LowRankData}
    {low Y : ℝ → ℝ} {K : ℝ≥0}
    (ha : 0 < a) (hax : a ≤ xHi) (hb : zStart ≤ b)
    (hlow : LipschitzOnWith K low (Icc a xHi)) :
    LipschitzOnWith K (completedVariationalScore a lam d low Y b) (Icc a xHi) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro r hr s hs
  rw [completedVariationalScore_low ha hax hb hr,completedVariationalScore_low ha hax hb hs]
  exact hlow.dist_le_mul r hr s hs

 theorem completedVariationalScore_rank_graph {lam a b : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (hd : Admissible lam d) (ha : 0 < a) (hax : a ≤ xLo) (hb : zStart ≤ b)
    (hlow : Continuous low) (heq : d.phi =ᵐ[volume.restrict (Icc xLo xHi)] low) :
    ∀ r ∈ Icc xLo xHi,(r,completedVariationalScore a lam d low Y b r) ∈ rankScoreSupport d.phi := by
  intro r hr
  have hxx : xLo < xHi := by norm_num [xLo,xHi]
  rw [completedVariationalScore_low ha (hax.trans hxx.le) hb ⟨hax.trans hr.1,hr.2⟩]
  exact hd.continuous_rep_score_mem hxx le_rfl le_rfl hlow
    (ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self heq) hr

 theorem completedVariationalScore_verifier {lam a b : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (ha : 0 < a) (hax : a ≤ xHi) (hb : b ∈ Icc zStart zEnd)
    (hlow : ContinuousOn low (Icc a xHi)) (hanti : StrictAntiOn low (Icc a xHi))
    (hceiling : ∀ r ∈ Icc a xHi,low r ≤ lam-r)
    (hxjoin : low xHi=lam-xHi) (hzjoin : continuationScore lam d Y zStart=lam-zStart)
    (hprimitive : cap lam d.S a+(∫ t in a..xHi,low t)=quadratic lam xHi-d.S)
    (hactive : ∀ r ∈ Icc zStart b,∀ v ∈ controlFeatureSupport d,
      featureH hd r (Y r) v=vectorField lam d r (Y r) →
      vectorField lam d r (Y r) ≠ lam-r →
      1 ≤ featureTheta lam d v+featureAlpha lam d v*v.1.1)
    (hhead : headSlope a (cap lam d.S a) (low a) < 0)
    (hhead0 : headInitial a (cap lam d.S a) (low a) ≤ lam)
    (htail1 : tailOne b (Y b) (continuationScore lam d Y b) ≤ b-1)
    (htail2 : tailTwo b (Y b) (continuationScore lam d Y b) ≤ 0) :
    VerifierCurve (completedVariationalScore a lam d low Y b) lam := by
  have hL := hd.1
  have hxl : xHi ≤ lam := by norm_num [lambdaLo,xHi] at hL ⊢; linarith
  have hlz : lam ≤ zStart := by norm_num [lambdaHi,zStart] at hL ⊢; linarith
  have hb1 : b < 1 := hb.2.trans_lt (by norm_num [zEnd])
  have hshape := continuation_score_concave hd hY le_rfl hb.2 hactive
  have hc := middleScore_continuousOn hd hY hb.2 hlow hxjoin hzjoin
  have hm := middleScore_strictAntiOn hax hb.1 hanti hshape.1 hxjoin hzjoin
  have harea := middleScore_high_integral hd hY hax hb hlow hxjoin hzjoin hprimitive
  apply completedScore_verifierCurve (by
    constructor <;> norm_num [lambdaLo,lambdaHi] at hL <;> linarith)
    ha (hax.trans hxl) (hlz.trans hb.1) hb1 hc hm
    (middleScore_low _ _ _ _ hax) (middleScore_high hxjoin hzjoin hb.1)
  · rw [middleScore_line hxjoin ⟨hxl,hlz⟩]
    ring
  · linarith
  · exact hhead
  · exact hhead0
  · exact htail1
  · exact htail2
  · exact middleScore_ceiling hceiling
  · exact middleScore_high_fall hxl hlz hb.1 hxjoin hzjoin hshape.1

 theorem completedVariationalScore_low_primitive {lam a b : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (ha : 0 < a) (hax : a ≤ xHi) (hb : b ∈ Icc zStart zEnd)
    (hlow : ContinuousOn low (Icc a xHi))
    (hxjoin : low xHi=lam-xHi) (hzjoin : continuationScore lam d Y zStart=lam-zStart)
    (hprimitive : ∀ r ∈ Icc a xHi,primitive lam d r=cap lam d.S a+∫ t in a..r,low t) :
    ∀ r ∈ Icc a xHi,curvePrimitive (completedVariationalScore a lam d low Y b) r=primitive lam d r := by
  intro r hr
  have hxb : xHi ≤ b := (by norm_num [xHi,zStart] : xHi ≤ zStart).trans hb.1
  rw [completedVariationalScore,completedScore_middle_primitive ha (hax.trans hxb)
    (hb.2.trans (by norm_num [zEnd])) (middleScore_continuousOn hd hY hb.2 hlow hxjoin hzjoin)
    (middleScore_low _ _ _ _ hax) (middleScore_high hxjoin hzjoin hb.1) ⟨hr.1,hr.2.trans hxb⟩,
    middleScore_low_integral hr,hprimitive r hr]

 theorem completedVariationalScore_high_primitive {lam a b : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (ha : 0 < a) (hax : a ≤ xHi) (hb : b ∈ Icc zStart zEnd)
    (hlow : ContinuousOn low (Icc a xHi))
    (hxjoin : low xHi=lam-xHi) (hzjoin : continuationScore lam d Y zStart=lam-zStart)
    (hprimitive : cap lam d.S a+(∫ t in a..xHi,low t)=quadratic lam xHi-d.S) :
    ∀ r ∈ Icc zStart b,curvePrimitive (completedVariationalScore a lam d low Y b) r=Y r := by
  intro r hr
  have hxz : xHi ≤ zStart := by norm_num [xHi,zStart]
  rw [completedVariationalScore,completedScore_middle_primitive ha (hax.trans (hxz.trans hb.1))
    (hb.2.trans (by norm_num [zEnd])) (middleScore_continuousOn hd hY hb.2 hlow hxjoin hzjoin)
    (middleScore_low _ _ _ _ hax) (middleScore_high hxjoin hzjoin hb.1) ⟨hax.trans (hxz.trans hr.1),hr.2⟩]
  exact middleScore_high_integral hd hY hax ⟨hr.1,hr.2.trans hb.2⟩ hlow hxjoin hzjoin hprimitive


 theorem completedVariationalScore_line_primitive {lam a b : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (ha : 0 < a) (hax : a ≤ xHi) (hb : b ∈ Icc zStart zEnd)
    (hlow : ContinuousOn low (Icc a xHi))
    (hxjoin : low xHi=lam-xHi) (hzjoin : continuationScore lam d Y zStart=lam-zStart)
    (hprimitive : cap lam d.S a+(∫ t in a..xHi,low t)=quadratic lam xHi-d.S) :
    ∀ r ∈ Icc xHi zStart,
      curvePrimitive (completedVariationalScore a lam d low Y b) r=quadratic lam r-d.S := by
  intro r hr
  have hxz : xHi ≤ zStart := by norm_num [xHi,zStart]
  rw [completedVariationalScore,completedScore_middle_primitive ha (hax.trans (hxz.trans hb.1))
    (hb.2.trans (by norm_num [zEnd])) (middleScore_continuousOn hd hY hb.2 hlow hxjoin hzjoin)
    (middleScore_low _ _ _ _ hax) (middleScore_high hxjoin hzjoin hb.1) ⟨hax.trans hr.1,hr.2.trans hb.1⟩]
  exact middleScore_line_integral hd hY hax hr hlow hxjoin hzjoin hprimitive

 theorem completedVariationalScore_cap_before_contact {lam a b c : ℝ} {d : LowRankData} {psi Y : ℝ → ℝ}
    (ha : 0 < a) (hac : a ≤ c) (hcx : c ≤ xHi) (hb : zStart ≤ b) :
    ∀ r ∈ Icc a c,
      completedVariationalScore a lam d (capRegularScore lam d.S c psi) Y b r=capScore lam d.S r := by
  intro r hr
  rw [completedVariationalScore_low ha (hac.trans hcx) hb ⟨hr.1,hr.2.trans hcx⟩,
    capRegularScore_left _ _ _ _ hr.2]

end OptimalG.Variational
