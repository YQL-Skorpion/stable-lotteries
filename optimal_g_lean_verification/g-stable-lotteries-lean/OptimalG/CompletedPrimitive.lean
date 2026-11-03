import OptimalG.CompletedCurve

/-! The completed score has the intended actual integral primitive on the
middle interval and on the polynomial tail. -/
namespace OptimalG
open Set MeasureTheory

theorem completedScore_middle_primitive {x J f z Y H r : ℝ} {psi : ℝ → ℝ}
    (hx : 0 < x) (hxz : x ≤ z) (hz : z ≤ 1) (hpsi : ContinuousOn psi (Icc x z))
    (hxjoin : psi x=f) (hzjoin : psi z=H) (hr : r ∈ Icc x z) :
    curvePrimitive (completedScore x J f z Y H psi) r=J+∫ t in x..r,psi t := by
  have hc := completedScore_continuousOn (J := J) (Y := Y) hx.ne' hxz hpsi hxjoin hzjoin
  have h0r : (0 : ℝ) ≤ r := hx.le.trans hr.1
  have hi : IntervalIntegrable (completedScore x J f z Y H psi) volume 0 1 :=
    hc.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hix := hi.mono_set (by
    rw [uIcc_of_le hx.le,uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl (hxz.trans hz))
  have hir := hi.mono_set (by
    rw [uIcc_of_le hr.1,uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hx.le (hr.2.trans hz))
  unfold curvePrimitive
  rw [← intervalIntegral.integral_add_adjacent_intervals hix hir]
  have hh : (∫ t in (0 : ℝ)..x,completedScore x J f z Y H psi t)=J :=
    completedScore_head_integral hx
  rw [hh]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hr.1] at ht
  exact completedScore_middle hx.ne' hxz hxjoin ⟨ht.1,ht.2.trans hr.2⟩

theorem completedScore_tail_primitive {x J f z Y H r : ℝ} {psi : ℝ → ℝ}
    (hx : 0 < x) (hxz : x ≤ z) (hz : z < 1) (hpsi : ContinuousOn psi (Icc x z))
    (hxjoin : psi x=f) (hzjoin : psi z=H) (harea : (∫ t in x..z,psi t)=Y-J)
    (hr : r ∈ Icc z 1) :
    curvePrimitive (completedScore x J f z Y H psi) r=tailPrimitive z Y H r := by
  have hc := completedScore_continuousOn (J := J) (Y := Y) hx.ne' hxz hpsi hxjoin hzjoin
  have hz0 : (0 : ℝ) ≤ z := hx.le.trans hxz
  have hi : IntervalIntegrable (completedScore x J f z Y H psi) volume 0 1 :=
    hc.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hiz := hi.mono_set (by
    rw [uIcc_of_le hz0,uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hz.le)
  have hir := hi.mono_set (by
    rw [uIcc_of_le hr.1,uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hz0 hr.2)
  have hmid := completedScore_middle_primitive (J := J) (Y := Y) hx hxz hz.le hpsi hxjoin hzjoin ⟨hxz,le_rfl⟩
  rw [harea] at hmid
  have hmid' : curvePrimitive (completedScore x J f z Y H psi) z=Y := by linarith
  have htail : (∫ t in z..r,completedScore x J f z Y H psi t)=tailPrimitive z Y H r-Y := by
    calc
      _ = ∫ t in z..r,tailScore z Y H t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hr.1] at ht
        exact completedScore_tail hx.ne' hxz hxjoin hzjoin ht.1
      _ = _ := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => tailPrimitive_hasDerivAt z Y H t hz.ne)
          ((tailScore_continuous z Y H).intervalIntegrable z r),tailPrimitive_at_join]
  unfold curvePrimitive
  rw [← intervalIntegral.integral_add_adjacent_intervals hiz hir]
  change curvePrimitive (completedScore x J f z Y H psi) z+_ = _
  rw [hmid',htail]
  ring

end OptimalG
