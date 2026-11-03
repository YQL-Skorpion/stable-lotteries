import OptimalG.Certificates.TransportSegments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The rank densities in B.4 are defined by the actual affine control maps.
Weights are functions of high rank; each summand retains its own exact slope.
The calculus and Fubini identities are supplied separately. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

noncomputable def segmentDensity (seg : ReferenceSegment) (rank : ReferenceNode → ℚ)
    (weight : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r∈Ioo (rank seg.left:ℝ) (rank seg.right:ℝ) then
    weight (seg.inverseRankMap rank r)/(seg.slope rank:ℝ)
  else 0

noncomputable def pushforwardDensity (segments : List ReferenceSegment)
    (rank : ReferenceNode → ℚ) (weight : ReferenceSegment → ℝ → ℝ) (r : ℝ) : ℝ :=
  (segments.map (fun seg => segmentDensity seg rank (weight seg) r)).sum

/-- Derivative/entropy flux density: r-allocated and a-allocated weights are
pushed forward through their respective exact control maps. -/
noncomputable def W (segments : List ReferenceSegment)
    (weightR weightA : ReferenceSegment → ℝ → ℝ) (r : ℝ) : ℝ :=
  pushforwardDensity segments ReferenceNode.r weightR r+
    pushforwardDensity segments ReferenceNode.a weightA r

/-- Positional first-variation density, with the same rank-map Jacobians. -/
noncomputable def f (segments : List ReferenceSegment)
    (positionR positionA : ReferenceSegment → ℝ → ℝ) (r : ℝ) : ℝ :=
  pushforwardDensity segments ReferenceNode.r positionR r+
    pushforwardDensity segments ReferenceNode.a positionA r

/-- The continuous cumulative positional coefficient used by flux absorption. -/
noncomputable def P1 (segments : List ReferenceSegment)
    (positionR positionA : ReferenceSegment → ℝ → ℝ) (rightContact r : ℝ) : ℝ :=
  ∫ s in r..rightContact, f segments positionR positionA s

end OptimalG.Certificates.Transport
