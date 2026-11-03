import OptimalG.IntervalGlue

/-! The actual polynomial completion of a continuous middle score. -/
namespace OptimalG
open Set MeasureTheory

noncomputable def completedScore (x J f z Y H : ℝ) (psi : ℝ → ℝ) : ℝ → ℝ :=
  joinAt x (headScore x J f) (joinAt z psi (tailScore z Y H))

theorem completedScore_middle {x J f z Y H r : ℝ} {psi : ℝ → ℝ}
    (hx : x ≠ 0) (hxz : x ≤ z) (hjoin : psi x=f) (hr : r ∈ Icc x z) :
    completedScore x J f z Y H psi r=psi r := by
  have hj : headScore x J f x=joinAt z psi (tailScore z Y H) x := by
    rw [headScore_at_join x J f hx,joinAt_left _ _ hxz,hjoin]
  rw [completedScore,joinAt_right _ _ hr.1 hj,joinAt_left _ _ hr.2]

theorem completedScore_tail {x J f z Y H r : ℝ} {psi : ℝ → ℝ}
    (hx : x ≠ 0) (hxz : x ≤ z) (hxjoin : psi x=f) (hzjoin : psi z=H) (hr : z ≤ r) :
    completedScore x J f z Y H psi r=tailScore z Y H r := by
  have hj : headScore x J f x=joinAt z psi (tailScore z Y H) x := by
    rw [headScore_at_join x J f hx,joinAt_left _ _ hxz,hxjoin]
  have hk : psi z=tailScore z Y H z := by simpa using hzjoin
  rw [completedScore,joinAt_right _ _ (hxz.trans hr) hj,joinAt_right _ _ hr hk]

theorem completedScore_continuousOn {x J f z Y H : ℝ} {psi : ℝ → ℝ}
    (hx : x ≠ 0) (hxz : x ≤ z) (hpsi : ContinuousOn psi (Icc x z))
    (hxjoin : psi x=f) (hzjoin : psi z=H) :
    ContinuousOn (completedScore x J f z Y H psi) (Icc 0 1) := by
  have hk : psi z=tailScore z Y H z := by simpa using hzjoin
  have hi := continuousOn_joinAt (b := 1) hpsi (tailScore_continuous z Y H).continuousOn hk
  have hj : headScore x J f x=joinAt z psi (tailScore z Y H) x := by
    rw [headScore_at_join x J f hx,joinAt_left _ _ hxz,hxjoin]
  exact continuousOn_joinAt (headScore_continuous x J f).continuousOn hi hj

theorem completedScore_strictAntiOn {x J f z Y H : ℝ} {psi : ℝ → ℝ}
    (hx : 0 < x) (hxz : x ≤ z) (hz : z < 1)
    (hhead : headSlope x J f < 0) (htail1 : tailOne z Y H < 0) (htail2 : tailTwo z Y H ≤ 0)
    (hpsi : StrictAntiOn psi (Icc x z)) (hxjoin : psi x=f) (hzjoin : psi z=H) :
    StrictAntiOn (completedScore x J f z Y H psi) (Icc 0 1) := by
  have hk : psi z=tailScore z Y H z := by simpa using hzjoin
  have hi := strictAntiOn_joinAt hxz hz.le hpsi
    (tailScore_strictAntiOn z Y H hz htail1 htail2) hk
  have hj : headScore x J f x=joinAt z psi (tailScore z Y H) x := by
    rw [headScore_at_join x J f hx.ne',joinAt_left _ _ hxz,hxjoin]
  exact strictAntiOn_joinAt hx.le (hxz.trans hz.le) ((headScore_strictAnti x J f hhead).strictAntiOn (Icc 0 x)) hi hj

theorem completedScore_integral_zero {x J f z Y H : ℝ} {psi : ℝ → ℝ}
    (hx : 0 < x) (hxz : x ≤ z) (hz : z < 1) (hpsi : ContinuousOn psi (Icc x z))
    (hxjoin : psi x=f) (hzjoin : psi z=H) (harea : (∫ r in x..z,psi r)=Y-J) :
    (∫ r in (0 : ℝ)..1,completedScore x J f z Y H psi r)=0 := by
  have hk : psi z=tailScore z Y H z := by simpa using hzjoin
  have hi := continuousOn_joinAt (b := 1) hpsi (tailScore_continuous z Y H).continuousOn hk
  have hj : headScore x J f x=joinAt z psi (tailScore z Y H) x := by
    rw [headScore_at_join x J f hx.ne',joinAt_left _ _ hxz,hxjoin]
  rw [completedScore,integral_joinAt hx.le (hxz.trans hz.le)
    (headScore_continuous x J f).continuousOn hi hj,
    integral_joinAt hxz hz.le hpsi (tailScore_continuous z Y H).continuousOn hk,
    headScore_integral x J f hx.ne',tailScore_integral z Y H hz.ne,harea]
  ring

theorem completedScore_at_one {x J f z Y H : ℝ} {psi : ℝ → ℝ}
    (hx : x ≠ 0) (hxz : x ≤ z) (hz : z < 1) (hxjoin : psi x=f) (hzjoin : psi z=H) :
    completedScore x J f z Y H psi 1 = -1 := by
  rw [completedScore_tail hx hxz hxjoin hzjoin hz.le,tailScore_at_one z Y H hz.ne]

theorem completedScore_head_integral {x J f z Y H : ℝ} {psi : ℝ → ℝ} (hx : 0 < x) :
    curvePrimitive (completedScore x J f z Y H psi) x=J := by
  rw [curvePrimitive]
  calc
    _ = ∫ r in (0 : ℝ)..x,headScore x J f r := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hx.le] at hr
      exact joinAt_left _ _ hr.2
    _ = J := headScore_integral x J f hx.ne'

end OptimalG
