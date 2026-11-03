import OptimalG.Certificates.ReferenceFlowPartition
import OptimalG.VariationalTransportCrop
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The positional first variation is the genuine rank pushforward of the
time forces. The test is cropped to the central matching interval. Thus a
fixed cap-prefix rank contributes zero, while an early central rank remains.
No vanishing positional force is assumed on the early branch. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory Variational

theorem ReferenceSegment.rankMap_mem_Ioo_real (seg : ReferenceSegment)
    (rank : ReferenceNode→ℚ) (ht : (seg.left.z:ℝ)<seg.right.z)
    (hr : (rank seg.left:ℝ)<rank seg.right) {z : ℝ}
    (hz : z∈Ioo (seg.left.z:ℝ) seg.right.z) :
    seg.rankMap rank z∈Ioo (rank seg.left:ℝ) (rank seg.right:ℝ) := by
  have hs : (0:ℝ)<seg.slope rank := by
    simp only [ReferenceSegment.slope,Rat.cast_div,Rat.cast_sub]
    exact div_pos (sub_pos.mpr hr) (sub_pos.mpr ht)
  have he : (seg.slope rank:ℝ)*((seg.right.z:ℝ)-seg.left.z)=
      (rank seg.right:ℝ)-rank seg.left := by
    simp only [ReferenceSegment.slope,Rat.cast_div,Rat.cast_sub]
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr ht.ne')
  simp only [ReferenceSegment.rankMap,mem_Ioo]
  constructor
  · nlinarith only [mul_pos hs (sub_pos.mpr hz.1)]
  · nlinarith only [he,mul_pos hs (sub_pos.mpr hz.2)]

/-- Any integrable central-rank test pulls back through an actual affine
reference segment. The test may be unbounded; in particular this applies
to the Stieltjes derivative and its entropy. -/
theorem reference_cropped_test_pullback_integrable (seg : ReferenceSegment)
    (rank : ReferenceNode→ℚ) {test : ℝ→ℝ} {a b : ℝ}
    (ht : (seg.left.z:ℝ)<seg.right.z) (hr : (rank seg.left:ℝ)<rank seg.right)
    (hi : IntegrableOn test (Icc a b)) :
    Integrable (fun z=>(Icc a b).indicator test (seg.rankMap rank z)) := by
  have hs : (seg.slope rank:ℝ)≠0 := by
    apply ne_of_gt
    simp only [ReferenceSegment.slope,Rat.cast_div,Rat.cast_sub]
    exact div_pos (sub_pos.mpr hr) (sub_pos.mpr ht)
  have hg := ((hi.integrable_indicator measurableSet_Icc).comp_add_left
    ((rank seg.left:ℝ)-(seg.slope rank:ℝ)*seg.left.z)).comp_mul_left' hs
  convert hg using 1
  funext z
  congr 1
  unfold ReferenceSegment.rankMap
  ring

theorem reference_cropped_test_mul_weight_integrable (seg : ReferenceSegment)
    (rank : ReferenceNode→ℚ) {test displacement force : ℝ→ℝ} {a b B : ℝ}
    (ht : (seg.left.z:ℝ)<seg.right.z) (hr : (rank seg.left:ℝ)<rank seg.right)
    (hi : IntegrableOn test (Icc a b))
    (hlocal : ∀ z∈Ioo (seg.left.z:ℝ) seg.right.z,
      displacement z=(Icc a b).indicator test (seg.rankMap rank z))
    (hforce : AEStronglyMeasurable force
      (volume.restrict (Ioo (seg.left.z:ℝ) seg.right.z)))
    (hbound : ∀ᵐ z ∂volume.restrict (Ioo (seg.left.z:ℝ) seg.right.z),|force z|≤B) :
    IntervalIntegrable (fun z=>displacement z*force z) volume (seg.left.z:ℝ) seg.right.z := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mpr
  have hp : IntegrableOn (fun z=>(Icc a b).indicator test (seg.rankMap rank z))
      (Ioo (seg.left.z:ℝ) seg.right.z) :=
    (reference_cropped_test_pullback_integrable seg rank ht hr hi).integrableOn
  apply (hp.mul_bdd hforce (by simpa only [Real.norm_eq_abs] using hbound)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  rw [hlocal z hz]

theorem segmentDensity_integrable_of_bounded (seg : ReferenceSegment)
    (rank : ReferenceNode→ℚ) (force : ℝ→ℝ) {B : ℝ} (hB : 0≤B)
    (hm : Measurable (segmentDensity seg rank force))
    (hb : ∀ r∈Ioo (rank seg.left:ℝ) (rank seg.right:ℝ),
      |segmentDensity seg rank force r|≤B) :
    Integrable (segmentDensity seg rank force) := by
  have hi : IntegrableOn (segmentDensity seg rank force)
      (Icc (rank seg.left:ℝ) (rank seg.right:ℝ)) := by
    apply (integrable_const B).mono' hm.aestronglyMeasurable
    filter_upwards [] with r
    rw [Real.norm_eq_abs]
    by_cases hr : r∈Ioo (rank seg.left:ℝ) (rank seg.right:ℝ)
    · exact hb r hr
    · simpa only [segmentDensity,if_neg hr,abs_zero] using hB
  have he : (Icc (rank seg.left:ℝ) (rank seg.right:ℝ)).indicator
      (segmentDensity seg rank force)=segmentDensity seg rank force := by
    funext r
    by_cases hr : r∈Icc (rank seg.left:ℝ) (rank seg.right:ℝ)
    · exact indicator_of_mem hr _
    · have ho : r∉Ioo (rank seg.left:ℝ) (rank seg.right:ℝ) :=
        fun h=>hr ⟨h.1.le,h.2.le⟩
      simp only [indicator_of_notMem hr,segmentDensity,if_neg ho]
  exact he ▸ hi.integrable_indicator measurableSet_Icc

theorem segmentDensity_cropped_displacement_integrable (seg : ReferenceSegment)
    (rank : ReferenceNode→ℚ) (force : ℝ→ℝ) {G : ℝ→ℝ} {a b B : ℝ}
    (hab : a≤b) (hG : Measurable G) (hmatch : ∀ r∈Icc a b,G r∈Icc a b)
    (hB : 0≤B) (hm : Measurable (segmentDensity seg rank force))
    (hb : ∀ r∈Ioo (rank seg.left:ℝ) (rank seg.right:ℝ),
      |segmentDensity seg rank force r|≤B) :
    Integrable (fun r=>segmentDensity seg rank force r*
      (Icc a b).indicator (fun r=>G r-r) r) := by
  apply (segmentDensity_integrable_of_bounded seg rank force hB hm hb).mul_bdd (c:=b-a)
    (((hG.sub measurable_id).indicator measurableSet_Icc).aestronglyMeasurable)
  filter_upwards [] with r
  rw [Real.norm_eq_abs]
  by_cases hr : r∈Icc a b
  · rw [indicator_of_mem hr]
    change |G r-r|≤b-a
    have hg := hmatch r hr
    apply abs_le.mpr
    constructor <;> linarith [hr.1,hr.2,hg.1,hg.2]
  · simpa only [indicator_of_notMem hr,abs_zero] using sub_nonneg.mpr hab

theorem segmentDensity_cropped_test_integrable (seg : ReferenceSegment)
    (rank : ReferenceNode→ℚ) (force test : ℝ→ℝ) {a b B : ℝ}
    (htest : IntegrableOn test (Icc a b)) (hB : 0≤B)
    (hm : Measurable (segmentDensity seg rank force))
    (hb : ∀ r∈Ioo (rank seg.left:ℝ) (rank seg.right:ℝ),
      |segmentDensity seg rank force r|≤B) :
    Integrable (fun r=>segmentDensity seg rank force r*(Icc a b).indicator test r) := by
  apply (htest.integrable_indicator measurableSet_Icc).bdd_mul hm.aestronglyMeasurable
  filter_upwards [] with r
  rw [Real.norm_eq_abs]
  by_cases hr : r∈Ioo (rank seg.left:ℝ) (rank seg.right:ℝ)
  · exact hb r hr
  · simpa only [segmentDensity,if_neg hr,abs_zero] using hB

theorem pushforward_cropped_test_integral (segments : List ReferenceSegment)
    (rank : ReferenceNode→ℚ) (force test : ℝ→ℝ) (a b : ℝ) :
    (∫ r,pushforwardDensity segments rank (fun _=>force) r*
      (Icc a b).indicator test r)=
      ∫ r in Icc a b,pushforwardDensity segments rank (fun _=>force) r*test r := by
  rw [←integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with r
  by_cases hr : r∈Icc a b
  · simp only [indicator_of_mem hr]
  · simp only [indicator_of_notMem hr,mul_zero]

/-- One rank coordinate, with a checked time cover and the exact local
displacement identity. Integrability premises are ordinary analytic bounds
on the actual force and displacement, not assumptions about an optimum. -/
theorem reference_positional_pushforward
    {start finish : ℚ} {cells : List ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish cells=true)
    (rank : ReferenceNode→ℚ) (displacement force test : ℝ→ℝ) (a b : ℝ)
    (hrank : ∀ c∈cells,(rank c.segment.left:ℝ)<rank c.segment.right)
    (hlocal : ∀ c∈cells,∀ z∈Ioo (c.segment.left.z:ℝ) c.segment.right.z,
      displacement z=(Icc a b).indicator test (c.segment.rankMap rank z))
    (htime : ∀ c∈cells,IntervalIntegrable (fun z=>displacement z*force z)
      volume (c.segment.left.z:ℝ) c.segment.right.z)
    (hdensity : ∀ c∈cells,Integrable (fun r=>segmentDensity c.segment rank force r*
      (Icc a b).indicator test r)) :
    IntervalIntegrable (fun z=>displacement z*force z) volume (start:ℝ) finish ∧
      (∫ z in (start:ℝ)..finish,displacement z*force z)=
      ∫ r in Icc a b,pushforwardDensity (cells.map (·.segment)) rank
        (fun _=>force) r*test r := by
  have hp := referenceFlow_partition_integral _ hc htime
  refine ⟨hp.1,?_⟩
  rw [←pushforward_cropped_test_integral]
  rw [pushforwardDensity_integral (cells.map (·.segment)) rank (fun _=>force)
    ((Icc a b).indicator test)]
  · rw [hp.2,List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hm
    have hpos : (c.segment.left.z:ℝ)<c.segment.right.z := by
      exact_mod_cast (referenceFlowCoverCheck_bounds hc hm).2.1
    apply intervalIntegral.integral_congr_Ioo_of_le hpos.le
    intro z hz
    dsimp only
    rw [hlocal c hm z hz,mul_comm]
  · intro seg hs
    obtain ⟨c,hm,rfl⟩ := List.mem_map.mp hs
    exact_mod_cast (referenceFlowCoverCheck_bounds hc hm).2.1
  · intro seg hs
    obtain ⟨c,hm,rfl⟩ := List.mem_map.mp hs
    exact hrank c hm
  · intro seg hs
    obtain ⟨c,hm,rfl⟩ := List.mem_map.mp hs
    exact hdensity c hm

/-- The two actual coordinate forces combine into the density `f` used by
the flux certificate. The same full segment list is retained on both sides;
the rank integral itself discards the fixed cap prefix. -/
theorem reference_two_positional_pushforwards
    {start finish : ℚ} {cells : List ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish cells=true)
    (displacementR displacementA forceR forceA test : ℝ→ℝ) (a b : ℝ)
    (hrankR : ∀ c∈cells,(c.segment.left.r:ℝ)<c.segment.right.r)
    (hrankA : ∀ c∈cells,(c.segment.left.a:ℝ)<c.segment.right.a)
    (hlocalR : ∀ c∈cells,∀ z∈Ioo (c.segment.left.z:ℝ) c.segment.right.z,
      displacementR z=(Icc a b).indicator test (c.segment.rankMap (·.r) z))
    (hlocalA : ∀ c∈cells,∀ z∈Ioo (c.segment.left.z:ℝ) c.segment.right.z,
      displacementA z=(Icc a b).indicator test (c.segment.rankMap (·.a) z))
    (htimeR : ∀ c∈cells,IntervalIntegrable (fun z=>displacementR z*forceR z)
      volume (c.segment.left.z:ℝ) c.segment.right.z)
    (htimeA : ∀ c∈cells,IntervalIntegrable (fun z=>displacementA z*forceA z)
      volume (c.segment.left.z:ℝ) c.segment.right.z)
    (hdensityR : ∀ c∈cells,Integrable (fun r=>segmentDensity c.segment (·.r) forceR r*
      (Icc a b).indicator test r))
    (hdensityA : ∀ c∈cells,Integrable (fun r=>segmentDensity c.segment (·.a) forceA r*
      (Icc a b).indicator test r)) :
    (∫ z in (start:ℝ)..finish,
      displacementR z*forceR z+displacementA z*forceA z)=
      ∫ r in Icc a b,f (cells.map (·.segment)) (fun _=>forceR)
        (fun _=>forceA) r*test r := by
  have hR := reference_positional_pushforward hc (·.r) displacementR forceR test a b
    hrankR hlocalR htimeR hdensityR
  have hA := reference_positional_pushforward hc (·.a) displacementA forceA test a b
    hrankA hlocalA htimeA hdensityA
  have hiR : Integrable (fun r=>pushforwardDensity (cells.map (·.segment)) (·.r)
      (fun _=>forceR) r*(Icc a b).indicator test r) := by
    apply pushforwardDensity_test_integrable
    intro seg hs
    obtain ⟨c,hm,rfl⟩ := List.mem_map.mp hs
    exact hdensityR c hm
  have hiA : Integrable (fun r=>pushforwardDensity (cells.map (·.segment)) (·.a)
      (fun _=>forceA) r*(Icc a b).indicator test r) := by
    apply pushforwardDensity_test_integrable
    intro seg hs
    obtain ⟨c,hm,rfl⟩ := List.mem_map.mp hs
    exact hdensityA c hm
  rw [intervalIntegral.integral_add hR.1 hA.1,hR.2,hA.2,
    ←pushforward_cropped_test_integral,←pushforward_cropped_test_integral,
    ←integral_add hiR hiA,←integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with r
  by_cases hr : r∈Icc a b
  · simp only [indicator_of_mem hr,f]
    ring
  · simp only [indicator_of_notMem hr,mul_zero,zero_add]

end OptimalG.Certificates.Transport
