import OptimalG.LargeSelectedPiecewise
import OptimalG.Certificates.LargeSelectedExpressions
import OptimalG.RationalStationaryCurve

/-! At mass .65 the low-split numerator is increasing through the head.
The delayed rank crosses the head, cap and flat envelope in that order. -/
namespace OptimalG
open Set Variational Certificates.LargeSelectedExpressions

theorem monotoneOn_interval_split {f : ℝ→ℝ} {a b c : ℝ}
    (hl : MonotoneOn f (Icc a (min b c)))
    (hr : MonotoneOn f (Icc (max a c) b)) : MonotoneOn f (Icc a b) := by
  have hneg : AntitoneOn (fun x=> -f x) (Icc a b) :=
    antitoneOn_interval_split
      (fun x hx y hy hxy=>neg_le_neg (hl hx hy hxy))
      (fun x hx y hy hxy=>neg_le_neg (hr hx hy hxy))
  intro x hx y hy hxy
  exact neg_le_neg_iff.mp (hneg hx hy hxy)

theorem largeSelected_rank_hasDerivAt {lam S p z q e du dl : ℝ}
    {lower upper : ℝ→ℝ} (hu : HasDerivAt upper du (z-p+q))
    (hl : HasDerivAt lower dl q) :
    HasDerivAt (fun r=>largeSelectedNumerator lam S z r e (lower r) upper p)
      (-areaSlope lam S p z+p*(du-dl)) q := by
  have hu' := hu.comp q ((hasDerivAt_id q).const_add (z-p))
  convert! ((((hasDerivAt_id q).const_sub p).mul_const (areaSlope lam S p z)).add
    ((hu'.sub hl).const_mul p)).sub_const
      ((quadratic lam p-S-p*(z-391/500)/2)*e) using 1 <;>
    dsimp [largeSelectedNumerator,areaSlope] <;> ring

theorem largeSelected_rank_branch_monotone {lam S p z e a b : ℝ}
    {upper du lower dl : ℝ→ℝ}
    (hu : ∀ q∈Icc a b,HasDerivAt upper (du (z-p+q)) (z-p+q))
    (hl : ∀ q∈Icc a b,HasDerivAt lower (dl q) q)
    (hn : ∀ q∈Icc a b,0≤ -areaSlope lam S p z+p*(du (z-p+q)-dl q)) :
    MonotoneOn (fun q=>largeSelectedNumerator lam S z q e (lower q) upper p) (Icc a b) := by
  have hd (q : ℝ) (hq : q∈Icc a b) :=
    largeSelected_rank_hasDerivAt (lam:=lam) (S:=S) (p:=p) (z:=z) (e:=e) (hu q hq) (hl q hq)
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun q hq=>(hd q hq).continuousAt.continuousWithinAt)
    (fun q hq=>(hd q (interior_subset hq)).differentiableAt.differentiableWithinAt)
  intro q hq
  rw [(hd q (interior_subset hq)).deriv]
  exact hn q (interior_subset hq)

theorem largeSelected_head_monotone {lam S z e : ℝ}
    (hz : z∈Icc (391/500:ℝ) (7/8))
    (hs : 0≤1+Certificates.SmallMassExpressions.slope lam S)
    (hcapOrder : ∀ u∈Icc (0:ℝ) (9/25),∀ v∈Icc (0:ℝ) (9/25),u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤capScore lam S v-capScore lam S u)
    (hh : 0≤headHeadDerivative lam S z) (hf : 0≤headFlatDerivative lam S z) :
    MonotoneOn (fun q=>largeSelectedNumerator lam S z q e (largeHeadRemaining lam S q)
      (largeRemainingUpper lam S (Certificates.SmallMassExpressions.initial lam S)
        (Certificates.SmallMassExpressions.slope lam S)) (13/20)) (Icc (0:ℝ) (527/2000)) := by
  let U := largeRemainingUpper lam S (Certificates.SmallMassExpressions.initial lam S)
    (Certificates.SmallMassExpressions.slope lam S)
  let dl := fun r=>Certificates.SmallMassExpressions.initial lam S-lam+
    (1+Certificates.SmallMassExpressions.slope lam S)*r
  let a := 527/2000-z+13/20
  let b := 313/1000-z+13/20
  have hj := headScore_at_join (527/2000) (cap lam S (527/2000))
    (capScore lam S (527/2000)) (by norm_num)
  change Certificates.SmallMassExpressions.initial lam S+
    Certificates.SmallMassExpressions.slope lam S*(527/2000)=capScore lam S (527/2000) at hj
  apply monotoneOn_interval_split (c:=a)
  · have hhead {q : ℝ} (hq : q∈Icc (0:ℝ) (min (527/2000) a)) : z-13/20+q≤527/2000 := by
      have hqa := (le_min_iff.mp hq.2).2
      dsimp [a] at hqa
      linarith only [hqa]
    have hm := largeSelected_rank_branch_monotone (lam:=lam) (S:=S) (p:=13/20) (z:=z) (e:=e)
      (upper:=largeHeadRemaining lam S) (du:=dl) (lower:=largeHeadRemaining lam S) (dl:=dl)
      (a:=0) (b:=min (527/2000) a)
      (fun q _=>largeHeadRemaining_hasDerivAt lam S (z-13/20+q))
      (fun q _=>largeHeadRemaining_hasDerivAt lam S q) (by
        intro q _
        convert! hh using 1 <;> dsimp [headHeadDerivative,dl] <;> ring)
    intro x hx y hy hxy
    have hxy' := hm hx hy hxy
    simpa only [largeSelectedNumerator,U,largeRemainingUpper_eq_head (hhead hx),
      largeRemainingUpper_eq_head (hhead hy)] using hxy'
  · apply monotoneOn_interval_split (c:=b)
    · have hcap {q : ℝ} (hq : q∈Icc (max 0 a) (min (527/2000) b)) :
          z-13/20+q∈Icc (527/2000:ℝ) (313/1000) := by
        have hqa := (le_max_right _ _).trans hq.1
        have hqb := (le_min_iff.mp hq.2).2
        dsimp [a,b] at hqa hqb
        constructor <;> linarith only [hqa,hqb]
      have hm := largeSelected_rank_branch_monotone (lam:=lam) (S:=S) (p:=13/20) (z:=z) (e:=e)
        (upper:=capDeficit lam S) (du:=fun r=> -capSlack lam S r)
        (lower:=largeHeadRemaining lam S) (dl:=dl)
        (a:=max 0 a) (b:=min (527/2000) b)
        (fun q hq=>capDeficit_hasDerivAt lam S (z-13/20+q) (by linarith only [(hcap hq).2]))
        (fun q _=>largeHeadRemaining_hasDerivAt lam S q) (by
          intro q hq
          have hc := hcapOrder (527/2000) ⟨by norm_num,by norm_num⟩ (z-13/20+q)
            ⟨by linarith only [(hcap hq).1],by linarith only [(hcap hq).2]⟩ (hcap hq).1
          dsimp [headHeadDerivative] at hh
          dsimp [dl,capSlack]
          nlinarith only [hh,hc,hj])
      intro x hx y hy hxy
      have hxy' := hm hx hy hxy
      simpa only [largeSelectedNumerator,U,largeRemainingUpper_eq_cap (hcap hx),
        largeRemainingUpper_eq_cap (hcap hy)] using hxy'
    · have hflat {q : ℝ} (hq : q∈Icc (max (max 0 a) b) (527/2000)) :
          313/1000≤z-13/20+q := by
        have hqb := (le_max_right _ _).trans hq.1
        dsimp [b] at hqb
        linarith only [hqb]
      have hm := largeSelected_rank_branch_monotone (lam:=lam) (S:=S) (p:=13/20) (z:=z) (e:=e)
        (upper:=fun _=>capDeficit lam S (313/1000)) (du:=fun _=>0)
        (lower:=largeHeadRemaining lam S) (dl:=dl)
        (a:=max (max 0 a) b) (b:=527/2000)
        (fun q _=>hasDerivAt_const (z-13/20+q) _)
        (fun q _=>largeHeadRemaining_hasDerivAt lam S q) (by
          intro q hq
          have hmul := mul_nonneg hs (sub_nonneg.mpr hq.2)
          dsimp [headFlatDerivative,capSlack] at hf
          dsimp [dl]
          nlinarith only [hf,hj,hmul])
      intro x hx y hy hxy
      have hxy' := hm hx hy hxy
      simpa only [largeSelectedNumerator,U,largeRemainingUpper_eq_flat (hflat hx),
        largeRemainingUpper_eq_flat (hflat hy)] using hxy'

end OptimalG
