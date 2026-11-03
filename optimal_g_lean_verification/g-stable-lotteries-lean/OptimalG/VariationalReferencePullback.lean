import OptimalG.VariationalRankMatching
import OptimalG.VariationalAffinePushforward

/-! Exceptional low-rank sets remain null along every actual affine
reference segment, including after composition with the monotone matching. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped NNReal

 theorem ae_affine_pullback {c d : ℝ} (hc : 0 < c) {P : ℝ → Prop}
    (hP : ∀ᵐ r ∂volume, P r) : ∀ᵐ s ∂volume, P (c*s+d) := by
  let K : ℝ≥0 := ⟨1/c,by positivity⟩
  have hinj : InjOn (fun s : ℝ => c*s+d) univ := by
    intro s hs t ht he
    nlinarith only [he,hc]
  have hinverse : ∀ s ∈ (univ : Set ℝ), ∀ t ∈ univ,
      dist s t ≤ (K:ℝ)*dist (c*s+d) (c*t+d) := by
    intro s hs t ht
    have he : c*s+d-(c*t+d) = c*(s-t) := by ring
    rw [Real.dist_eq,Real.dist_eq,he,abs_mul,abs_of_pos hc]
    change |s-t| ≤ (1/c)*(c*|s-t|)
    rw [← mul_assoc,one_div_mul_cancel hc.ne',one_mul]
  have h := ae_pullback_of_inverse_lipschitz MeasurableSet.univ hinj hinverse hP
  simpa only [Measure.restrict_univ] using h

open Certificates.Transport in
 theorem reference_rankMap_bounds (seg : ReferenceSegment) (rank : ReferenceNode → ℚ)
    (htime : (seg.left.z:ℝ) < seg.right.z) (hrank : (rank seg.left:ℝ) < rank seg.right)
    {s : ℝ} (hs : s ∈ Icc (seg.left.z:ℝ) seg.right.z) :
    seg.rankMap rank s ∈ Icc (rank seg.left:ℝ) (rank seg.right:ℝ) := by
  have hc : 0 < (seg.slope rank:ℝ) := by
    unfold ReferenceSegment.slope
    push_cast
    exact div_pos (sub_pos.mpr hrank) (sub_pos.mpr htime)
  have hend : seg.rankMap rank (seg.right.z:ℝ) = rank seg.right := by
    have ht : (seg.right.z:ℝ)-(seg.left.z:ℝ) ≠ 0 := sub_ne_zero.mpr htime.ne'
    unfold ReferenceSegment.rankMap ReferenceSegment.slope
    push_cast
    field_simp
    ring
  constructor
  · unfold ReferenceSegment.rankMap
    have hh := mul_nonneg hc.le (sub_nonneg.mpr hs.1)
    linarith
  · rw [← hend]
    unfold ReferenceSegment.rankMap
    gcongr
    exact hs.2

open Certificates.Transport in
 theorem ae_reference_segment_pullback (seg : ReferenceSegment) (rank : ReferenceNode → ℚ)
    (htime : (seg.left.z:ℝ) < seg.right.z) (hrank : (rank seg.left:ℝ) < rank seg.right)
    {a b : ℝ} (hrange : Icc (rank seg.left:ℝ) (rank seg.right:ℝ) ⊆ Icc a b)
    {P : ℝ → Prop} (hP : ∀ᵐ r ∂volume.restrict (Icc a b), P r) :
    ∀ᵐ s ∂volume.restrict (Icc (seg.left.z:ℝ) seg.right.z), P (seg.rankMap rank s) := by
  have hc : 0 < (seg.slope rank:ℝ) := by
    unfold ReferenceSegment.slope
    push_cast
    exact div_pos (sub_pos.mpr hrank) (sub_pos.mpr htime)
  have hg : ∀ᵐ r ∂volume, r ∈ Icc a b → P r := (ae_restrict_iff' measurableSet_Icc).mp hP
  have h := ae_affine_pullback (d:=(rank seg.left:ℝ)-(seg.slope rank:ℝ)*seg.left.z) hc hg
  have he (s : ℝ) : (seg.slope rank:ℝ)*s+((rank seg.left:ℝ)-(seg.slope rank:ℝ)*seg.left.z) =
      seg.rankMap rank s := by unfold ReferenceSegment.rankMap; ring
  simp only [he] at h
  filter_upwards [ae_restrict_of_ae h,ae_restrict_mem measurableSet_Icc] with s hs hsi
  exact hs (hrange (reference_rankMap_bounds seg rank htime hrank hsi))

end OptimalG.Variational
