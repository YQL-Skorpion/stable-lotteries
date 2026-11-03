import OptimalG.VariationalTransportAllocation

/-! Positional terms on the early branch disappear because their matching
 displacement is zero, not because their rank derivative vanishes. This exact
 cropping identity is separate from the zero r-weight identity for entropy. -/
namespace OptimalG.Variational
open Set Certificates.Transport

 theorem segmentDensity_mul_test_zero (seg : ReferenceSegment) (rank : ReferenceNode→ℚ)
    (weight test : ℝ→ℝ) (r : ℝ)
    (hzero : ∀ x∈Ioo (rank seg.left:ℝ) (rank seg.right:ℝ),test x=0) :
    segmentDensity seg rank weight r*test r=0 := by
  by_cases hr : r∈Ioo (rank seg.left:ℝ) (rank seg.right:ℝ)
  · rw [hzero r hr,mul_zero]
  · simp only [segmentDensity,if_neg hr,zero_mul]

theorem pushforwardDensity_filter_test_zero (segments : List ReferenceSegment)
    (rank : ReferenceNode→ℚ) (weight : ReferenceSegment→ℝ→ℝ) (test : ℝ→ℝ)
    (keep : ReferenceSegment→Bool)
    (hzero : ∀ seg∈segments,keep seg=false→
      ∀ r∈Ioo (rank seg.left:ℝ) (rank seg.right:ℝ),test r=0) (r : ℝ) :
    pushforwardDensity (segments.filter keep) rank weight r*test r=
      pushforwardDensity segments rank weight r*test r := by
  induction segments with
  | nil => rfl
  | cons seg rest ih =>
    have hi := ih (fun s hs=>hzero s (List.mem_cons_of_mem seg hs))
    cases hk : keep seg
    · have hz := segmentDensity_mul_test_zero seg rank (weight seg) test r
        (hzero seg List.mem_cons_self hk)
      simpa only [List.filter_cons,hk,Bool.false_eq_true,↓reduceIte,pushforwardDensity,
        List.map_cons,List.sum_cons,add_mul,hz,zero_add] using hi
    · simpa only [List.filter_cons,hk,↓reduceIte,pushforwardDensity,
        List.map_cons,List.sum_cons,add_mul] using
        congrArg (fun x=>segmentDensity seg rank (weight seg) r*test r+x) hi

theorem pushforwardDensity_filter_cropped_test (segments : List ReferenceSegment)
    (rank : ReferenceNode→ℚ) (weight : ReferenceSegment→ℝ→ℝ) (test : ℝ→ℝ)
    (keep : ReferenceSegment→Bool) {a b : ℝ}
    (hout : ∀ seg∈segments,keep seg=false→
      (rank seg.right:ℝ)≤a ∨ b≤(rank seg.left:ℝ)) (r : ℝ) :
    pushforwardDensity (segments.filter keep) rank weight r*(Icc a b).indicator test r=
      pushforwardDensity segments rank weight r*(Icc a b).indicator test r := by
  apply pushforwardDensity_filter_test_zero
  intro seg hs hk x hx
  apply indicator_of_notMem
  intro hxi
  rcases hout seg hs hk with hl | hu
  · exact (not_lt_of_ge hxi.1) (hx.2.trans_le hl)
  · exact (not_lt_of_ge hxi.2) (hu.trans_lt hx.1)

end OptimalG.Variational
