import OptimalG.Certificates.IntegerRounded
import OptimalG.Certificates.TransportSegments

/-! Exact Jacobian division for the two affine rank pushforwards. The
proposed interval is checked against rational endpoint cross products. -/
namespace OptimalG.Certificates
namespace IntegerInterval

def dividePositiveCheck (input output : IntegerInterval) (q : ℚ) : Bool :=
  decide (0<q ∧ q*(output.lo:ℚ)≤(input.lo:ℚ) ∧ (input.hi:ℚ)≤q*(output.hi:ℚ))

theorem dividePositiveCheck_sound {s : ℕ} {input output : IntegerInterval} {q : ℚ}
    (hc : dividePositiveCheck input output q=true) {x : ℝ} (hx : input.Contains s x) :
    output.Contains s (x/(q:ℝ)) := by
  have h : 0<q ∧ q*(output.lo:ℚ)≤(input.lo:ℚ) ∧ (input.hi:ℚ)≤q*(output.hi:ℚ) :=
    of_decide_eq_true hc
  have hq : (0:ℝ)<q := by exact_mod_cast h.1
  have hl : (q:ℝ)*(output.lo:ℝ)≤(input.lo:ℝ) := by exact_mod_cast h.2.1
  have hu : (input.hi:ℝ)≤(q:ℝ)*(output.hi:ℝ) := by exact_mod_cast h.2.2
  have he : (s:ℝ)*(x/(q:ℝ))=((s:ℝ)*x)/(q:ℝ) := by ring
  constructor
  · rw [he]
    exact (le_div_iff₀ hq).mpr (by nlinarith [hx.1])
  · rw [he]
    exact (div_le_iff₀ hq).mpr (by nlinarith [hx.2])

end IntegerInterval
namespace Transport

structure ReferenceDensityCell where
  segment : ReferenceSegment
  useR : Bool
  position : IntegerInterval
  weight : IntegerInterval
  mappedPosition : IntegerInterval
  mappedWeight : IntegerInterval

namespace ReferenceDensityCell

def rank (c : ReferenceDensityCell) : ReferenceNode→ℚ := if c.useR then (·.r) else (·.a)

def check (c : ReferenceDensityCell) : Bool :=
  IntegerInterval.dividePositiveCheck c.position c.mappedPosition (c.segment.slope c.rank) &&
    IntegerInterval.dividePositiveCheck c.weight c.mappedWeight (c.segment.slope c.rank)

theorem checked_densities {s : ℕ} (c : ReferenceDensityCell) (hc : c.check=true)
    {position weight : ℝ} (hp : c.position.Contains s position) (hw : c.weight.Contains s weight) :
    c.mappedPosition.Contains s (position/(c.segment.slope c.rank:ℝ)) ∧
    c.mappedWeight.Contains s (weight/(c.segment.slope c.rank:ℝ)) := by
  obtain ⟨hpos,hweight⟩ := Bool.and_eq_true_iff.mp hc
  exact ⟨IntegerInterval.dividePositiveCheck_sound hpos hp,
    IntegerInterval.dividePositiveCheck_sound hweight hw⟩

end ReferenceDensityCell
end Transport
end OptimalG.Certificates
