import OptimalG.VariationalLowCurve
import OptimalG.VariationalLineTail
import OptimalG.VariationalHighShape
import OptimalG.CompletedConcavity

/-! The actual middle score: the recovered low curve, the saturated line,
and the derivative of the variational continuation. The joining assumptions
are explicit scalar equalities; the primitive is proved from the actual ODE. -/
namespace OptimalG.Variational
open Set MeasureTheory

noncomputable def continuationScore (lam : ℝ) (d : LowRankData) (Y : ℝ → ℝ) (r : ℝ) : ℝ :=
  vectorField lam d r (Y r)

noncomputable def middleScore (lam : ℝ) (d : LowRankData) (low Y : ℝ → ℝ) : ℝ → ℝ :=
  joinAt xHi low (joinAt zStart (fun r => lam-r) (continuationScore lam d Y))

 theorem middleScore_low (lam : ℝ) (d : LowRankData) (low Y : ℝ → ℝ)
    {r : ℝ} (hr : r ≤ xHi) : middleScore lam d low Y r=low r :=
  joinAt_left _ _ hr

 theorem middleScore_line {lam r : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (hlow : low xHi=lam-xHi) (hr : r ∈ Icc xHi zStart) :
    middleScore lam d low Y r=lam-r := by
  have hxz : xHi ≤ zStart := by norm_num [xHi,zStart]
  rw [middleScore,joinAt_right _ _ hr.1 (by rw [joinAt_left _ _ hxz,hlow]),
    joinAt_left _ _ hr.2]

 theorem middleScore_high {lam r : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (hlow : low xHi=lam-xHi) (hstart : continuationScore lam d Y zStart=lam-zStart)
    (hr : zStart ≤ r) : middleScore lam d low Y r=continuationScore lam d Y r := by
  have hxz : xHi ≤ zStart := by norm_num [xHi,zStart]
  rw [middleScore,joinAt_right _ _ (hxz.trans hr) (by rw [joinAt_left _ _ hxz,hlow]),
    joinAt_right _ _ hr hstart.symm]

 theorem Admissible.continuationScore_continuousOn {lam : ℝ} {d : LowRankData} {Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y) :
    ContinuousOn (continuationScore lam d Y) (Icc zStart zEnd) :=
  hd.vectorField_continuous.comp_continuousOn (continuousOn_id.prodMk (continuation_continuous hY))

 theorem Admissible.continuationScore_integral {lam r : ℝ} {d : LowRankData} {Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y) (hr : r ∈ Icc zStart zEnd) :
    (∫ t in zStart..r,continuationScore lam d Y t)=Y r-(quadratic lam zStart-d.S) := by
  have hs : Icc zStart r ⊆ Icc zStart zEnd := Icc_subset_Icc le_rfl hr.2
  simpa only [continuationScore,hY.1] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1
    ((continuation_continuous hY).mono hs) (fun t ht =>
      (hY.2 t (hs ⟨ht.1.le,ht.2.le⟩)).hasDerivAt
        (Icc_mem_nhds ht.1 (ht.2.trans_le hr.2)))
    ((hd.continuationScore_continuousOn hY).mono hs |>.intervalIntegrable_of_Icc hr.1))

 theorem middleScore_continuousOn {lam a b : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y) (hb : b ≤ zEnd)
    (hlow : ContinuousOn low (Icc a xHi))
    (hxjoin : low xHi=lam-xHi) (hzjoin : continuationScore lam d Y zStart=lam-zStart) :
    ContinuousOn (middleScore lam d low Y) (Icc a b) := by
  apply continuousOn_joinAt hlow
    (continuousOn_joinAt (continuous_const.sub continuous_id).continuousOn
      ((hd.continuationScore_continuousOn hY).mono (Icc_subset_Icc le_rfl hb)) hzjoin.symm)
  rw [joinAt_left _ _ (by norm_num [xHi,zStart]),hxjoin]
  rfl

 theorem middleScore_strictAntiOn {lam a b : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (ha : a ≤ xHi) (hb : zStart ≤ b)
    (hlow : StrictAntiOn low (Icc a xHi))
    (hhigh : ∀ r ∈ Icc zStart b,∀ s ∈ Icc zStart b,r ≤ s →
      continuationScore lam d Y s-continuationScore lam d Y r ≤ r-s)
    (hxjoin : low xHi=lam-xHi) (hzjoin : continuationScore lam d Y zStart=lam-zStart) :
    StrictAntiOn (middleScore lam d low Y) (Icc a b) := by
  have hm : StrictAntiOn (fun r : ℝ => lam-r) (Icc xHi zStart) := by
    intro r hr s hs hrs
    linarith
  have hh : StrictAntiOn (continuationScore lam d Y) (Icc zStart b) := by
    intro r hr s hs hrs
    linarith [hhigh r hr s hs hrs.le]
  apply strictAntiOn_joinAt ha ((by norm_num [xHi,zStart] : xHi ≤ zStart).trans hb) hlow
    (strictAntiOn_joinAt (by norm_num [xHi,zStart]) hb hm hh hzjoin.symm)
  rw [joinAt_left _ _ (by norm_num [xHi,zStart]),hxjoin]

 theorem middleScore_ceiling {lam a b : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (hlow : ∀ r ∈ Icc a xHi,low r ≤ lam-r) :
    ∀ r ∈ Icc a b,middleScore lam d low Y r ≤ lam-r := by
  intro r hr
  by_cases hx : r ≤ xHi
  · rw [middleScore_low _ _ _ _ hx]
    exact hlow r ⟨hr.1,hx⟩
  · by_cases hz : r ≤ zStart
    · simp [middleScore,joinAt,hx,hz]
    · simp only [middleScore,joinAt,if_neg hx,if_neg hz]
      exact vectorField_le_line lam d r (Y r)

 theorem middleScore_high_fall {lam a b : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (ha : xHi ≤ a) (hab : a ≤ zStart) (hb : zStart ≤ b)
    (hxjoin : low xHi=lam-xHi) (hzjoin : continuationScore lam d Y zStart=lam-zStart)
    (hhigh : ∀ r ∈ Icc zStart b,∀ s ∈ Icc zStart b,r ≤ s →
      continuationScore lam d Y s-continuationScore lam d Y r ≤ r-s) :
    ∀ r s,a ≤ r → r ≤ s → s ≤ b →
      middleScore lam d low Y s-middleScore lam d low Y r ≤ r-s := by
  intro r s har hrs hsb
  by_cases hs : s ≤ zStart
  · rw [middleScore_line hxjoin ⟨ha.trans (har.trans hrs),hs⟩,
      middleScore_line hxjoin ⟨ha.trans har,hrs.trans hs⟩]
    ring_nf
    exact le_rfl
  · have hzs : zStart ≤ s := le_of_not_ge hs
    rw [middleScore_high hxjoin hzjoin hzs]
    by_cases hr : r ≤ zStart
    · rw [middleScore_line hxjoin ⟨ha.trans har,hr⟩]
      have hh := hhigh zStart ⟨le_rfl,hb⟩ s ⟨hzs,hsb⟩ hzs
      rw [hzjoin] at hh
      linarith
    · rw [middleScore_high hxjoin hzjoin (le_of_not_ge hr)]
      exact hhigh r ⟨le_of_not_ge hr,hrs.trans hsb⟩ s ⟨hzs,hsb⟩ hrs

 theorem middleScore_high_concave {lam a b : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (ha : xHi ≤ a) (haz : a ≤ zStart) (hb : zStart ≤ b)
    (hxjoin : low xHi=lam-xHi) (hzjoin : continuationScore lam d Y zStart=lam-zStart)
    (hhigh : ConcaveOn ℝ (Icc zStart b) (continuationScore lam d Y)) :
    ConcaveOn ℝ (Icc a b) (middleScore lam d low Y) := by
  have hline : ConcaveOn ℝ (Icc a zStart) (fun r : ℝ => lam-r) := by
    exact (concaveOn_const (c:=lam) (convex_Icc _ _)).sub
      (convexOn_id (convex_Icc _ _))
  have hh := concaveOn_joinAt_of_cross_slopes haz hb hline hhigh hzjoin.symm (by
    intro u hu v hv
    have hvline := vectorField_le_line lam d v (Y v)
    change continuationScore lam d Y v ≤ lam-v at hvline
    rw [hzjoin]
    have hl : ((lam-zStart)-(lam-u))/(zStart-u)= -1 := by
      field_simp [ne_of_gt (sub_pos.mpr hu.2)]
      ring
    rw [hl]
    apply (div_le_iff₀ (sub_pos.mpr hv.1)).mpr
    linarith)
  apply hh.congr
  intro r hr
  exact (joinAt_right _ _ (ha.trans hr.1) (by
    rw [joinAt_left _ _ (by norm_num [xHi,zStart]),hxjoin])).symm

 theorem middleScore_low_integral {lam a r : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (hr : r ∈ Icc a xHi) :
    (∫ t in a..r,middleScore lam d low Y t)=∫ t in a..r,low t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hr.1] at ht
  exact middleScore_low _ _ _ _ (ht.2.trans hr.2)

 theorem middleScore_high_integral {lam a r J : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (ha : a ≤ xHi) (hr : r ∈ Icc zStart zEnd)
    (hlow : ContinuousOn low (Icc a xHi))
    (hxjoin : low xHi=lam-xHi) (hzjoin : continuationScore lam d Y zStart=lam-zStart)
    (hlowArea : J+(∫ t in a..xHi,low t)=quadratic lam xHi-d.S) :
    J+(∫ t in a..r,middleScore lam d low Y t)=Y r := by
  have hxz : xHi ≤ zStart := by norm_num [xHi,zStart]
  have hhigh := (hd.continuationScore_continuousOn hY).mono (Icc_subset_Icc le_rfl hr.2)
  have hline : ContinuousOn (fun t : ℝ => lam-t) (Icc xHi zStart) :=
    (continuous_const.sub continuous_id).continuousOn
  have htail := continuousOn_joinAt hline hhigh hzjoin.symm
  have hjoin : low xHi=joinAt zStart (fun r => lam-r) (continuationScore lam d Y) xHi := by
    rw [joinAt_left _ _ hxz,hxjoin]
  rw [middleScore,integral_joinAt ha (hxz.trans hr.1) hlow htail hjoin,
    integral_joinAt hxz hr.1 hline hhigh hzjoin.symm,
    integral_line,hd.continuationScore_integral hY hr]
  linarith


 theorem middleScore_line_integral {lam a r J : ℝ} {d : LowRankData} {low Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (ha : a ≤ xHi) (hr : r ∈ Icc xHi zStart)
    (hlow : ContinuousOn low (Icc a xHi))
    (hxjoin : low xHi=lam-xHi) (hzjoin : continuationScore lam d Y zStart=lam-zStart)
    (hlowArea : J+(∫ t in a..xHi,low t)=quadratic lam xHi-d.S) :
    J+(∫ t in a..r,middleScore lam d low Y t)=quadratic lam r-d.S := by
  have hxz : xHi ≤ zStart := by norm_num [xHi,zStart]
  have hscore := middleScore_continuousOn hd hY
    (show r ≤ zEnd from hr.2.trans (by norm_num [zStart,zEnd])) hlow hxjoin hzjoin
  have hi1 : IntervalIntegrable (middleScore lam d low Y) volume a xHi :=
    (hscore.mono (Icc_subset_Icc le_rfl hr.1)).intervalIntegrable_of_Icc ha
  have hi2 : IntervalIntegrable (middleScore lam d low Y) volume xHi r :=
    (hscore.mono (Icc_subset_Icc ha le_rfl)).intervalIntegrable_of_Icc hr.1
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
    middleScore_low_integral ⟨ha,le_rfl⟩]
  have he : (∫ t in xHi..r,middleScore lam d low Y t)=quadratic lam r-quadratic lam xHi := by
    rw [← integral_line]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hr.1] at ht
    exact middleScore_line hxjoin ⟨ht.1,ht.2.trans hr.2⟩
  rw [he]
  linarith

end OptimalG.Variational
