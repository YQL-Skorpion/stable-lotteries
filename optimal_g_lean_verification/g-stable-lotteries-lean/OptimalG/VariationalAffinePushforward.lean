import OptimalG.Certificates.TransportPushforward
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! The exact change of variables for the certified piecewise-affine
reference control maps. No regularity of the test function is required. -/
namespace OptimalG.Variational
open Set MeasureTheory

 theorem affine_density_integral {a b c d : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (weight test : ℝ → ℝ) :
    (∫ r, (if r ∈ Ioo (c*a+d) (c*b+d) then weight ((r-d)/c)/c else 0)*test r) =
      ∫ s in a..b, weight s*test (c*s+d) := by
  let F := fun r => weight ((r-d)/c)*test r
  have hsub := intervalIntegral.integral_comp_mul_add F (a:=a) (b:=b) hc.ne' d
  have hR : (∫ s in a..b, F (c*s+d)) = ∫ s in a..b, weight s*test (c*s+d) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have he : ((c*s+d)-d)/c = s := by field_simp; ring
    simp only [F,he]
  have hleft : (∫ r, (if r ∈ Ioo (c*a+d) (c*b+d) then weight ((r-d)/c)/c else 0)*test r) =
      (∫ r in c*a+d..c*b+d, F r)/c := by
    have he : (fun r => (if r ∈ Ioo (c*a+d) (c*b+d) then weight ((r-d)/c)/c else 0)*test r) =
        (Ioo (c*a+d) (c*b+d)).indicator (fun r => F r/c) := by
      funext r
      by_cases hr : r ∈ Ioo (c*a+d) (c*b+d)
      · simp only [if_pos hr,indicator_of_mem hr,F]
        ring
      · simp only [if_neg hr,indicator_of_notMem hr,zero_mul]
    rw [he,integral_indicator measurableSet_Ioo,← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by nlinarith : c*a+d ≤ c*b+d),intervalIntegral.integral_div]
  rw [hleft]
  rw [hR] at hsub
  simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using hsub.symm

open Certificates.Transport in
/-- Specialization to the exact rational reference segments used by the
certificate data. -/
theorem reference_segment_density_integral (seg : ReferenceSegment) (rank : ReferenceNode → ℚ)
    (htime : (seg.left.z:ℝ) < seg.right.z) (hrank : (rank seg.left:ℝ) < rank seg.right)
    (weight test : ℝ → ℝ) :
    (∫ r, segmentDensity seg rank weight r*test r) =
      ∫ s in (seg.left.z:ℝ)..(seg.right.z:ℝ), weight s*test (seg.rankMap rank s) := by
  let c : ℝ := seg.slope rank
  let d : ℝ := (rank seg.left:ℝ)-c*seg.left.z
  have hc : 0 < c := by
    dsimp [c,ReferenceSegment.slope]
    push_cast
    exact div_pos (sub_pos.mpr hrank) (sub_pos.mpr htime)
  have hl : c*(seg.left.z:ℝ)+d = rank seg.left := by dsimp [d]; ring
  have hr : c*(seg.right.z:ℝ)+d = rank seg.right := by
    have ht : (seg.right.z:ℝ)-(seg.left.z:ℝ) ≠ 0 := sub_ne_zero.mpr htime.ne'
    dsimp [c,d,ReferenceSegment.slope]
    push_cast
    field_simp
    ring
  have hinv (r : ℝ) : seg.inverseRankMap rank r = (r-d)/c := by
    dsimp [ReferenceSegment.inverseRankMap,d]
    change (seg.left.z:ℝ)+(r-rank seg.left)/c = (r-((rank seg.left:ℝ)-c*seg.left.z))/c
    field_simp
    ring
  have hfwd (s : ℝ) : seg.rankMap rank s = c*s+d := by
    dsimp [ReferenceSegment.rankMap,c,d]
    ring
  have h := affine_density_integral (d:=d) htime.le hc weight test
  rw [hl,hr] at h
  simpa only [segmentDensity,hinv,hfwd] using h

end OptimalG.Variational
