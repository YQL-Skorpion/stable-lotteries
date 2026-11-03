import OptimalG.Certificates.ReferenceDensityCell
import OptimalG.Certificates.TransportPushforward

/-! Local time bounds become bounds on the actual affine pushforward
densities. The inverse map and its exact Jacobian remain in the conclusion.
-/
namespace OptimalG.Certificates.Transport
open Set

namespace ReferenceSegment

theorem inverseRankMap_mem {seg : ReferenceSegment} {rank : ReferenceNode→ℚ}
    (htime : seg.left.z<seg.right.z) (hslope : 0<seg.slope rank)
    {r : ℝ} (hr : r∈Ioo (rank seg.left:ℝ) (rank seg.right:ℝ)) :
    seg.inverseRankMap rank r∈Ioo (seg.left.z:ℝ) seg.right.z := by
  have hs : (0:ℝ)<seg.slope rank := by exact_mod_cast hslope
  have ht : (0:ℝ)<(seg.right.z:ℝ)-seg.left.z := by exact_mod_cast sub_pos.mpr htime
  have he : (rank seg.right:ℝ)-rank seg.left=
      (seg.slope rank:ℝ)*((seg.right.z:ℝ)-seg.left.z) := by
    simp only [slope,Rat.cast_div,Rat.cast_sub]
    field_simp [ht.ne']
  have hlo : 0<(r-(rank seg.left:ℝ))/(seg.slope rank:ℝ) :=
    div_pos (sub_pos.mpr hr.1) hs
  have hhi : (r-(rank seg.left:ℝ))/(seg.slope rank:ℝ)<
      (seg.right.z:ℝ)-seg.left.z := by
    apply (div_lt_iff₀ hs).mpr
    rw [mul_comm,←he]
    exact sub_lt_sub_right hr.2 _
  simp only [inverseRankMap,mem_Ioo]
  constructor <;> linarith

end ReferenceSegment
namespace ReferenceDensityCell

theorem checked_actual_densities {s : ℕ} (c : ReferenceDensityCell) (hc : c.check=true)
    (htime : c.segment.left.z<c.segment.right.z)
    (position weight : ℝ→ℝ)
    (hp : ∀ z∈Ioo (c.segment.left.z:ℝ) c.segment.right.z,c.position.Contains s (position z))
    (hw : ∀ z∈Ioo (c.segment.left.z:ℝ) c.segment.right.z,c.weight.Contains s (weight z))
    {r : ℝ} (hr : r∈Ioo (c.rank c.segment.left:ℝ) (c.rank c.segment.right:ℝ)) :
    c.mappedPosition.Contains s (segmentDensity c.segment c.rank position r) ∧
    c.mappedWeight.Contains s (segmentDensity c.segment c.rank weight r) := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hpos : 0<c.segment.slope c.rank := by
    exact (of_decide_eq_true hh.1 : 0<c.segment.slope c.rank ∧
      c.segment.slope c.rank*(c.mappedPosition.lo:ℚ)≤(c.position.lo:ℚ) ∧
      (c.position.hi:ℚ)≤c.segment.slope c.rank*(c.mappedPosition.hi:ℚ)).1
  have hz := ReferenceSegment.inverseRankMap_mem htime hpos hr
  simpa only [segmentDensity,if_pos hr] using
    c.checked_densities hc (hp _ hz) (hw _ hz)

end ReferenceDensityCell
end OptimalG.Certificates.Transport
