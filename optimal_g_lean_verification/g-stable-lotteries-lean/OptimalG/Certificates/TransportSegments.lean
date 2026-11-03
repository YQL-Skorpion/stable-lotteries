import OptimalG.Certificates.Interval

/-! Exact affine reference-control segments. The original rational endpoints
and each transport slope are retained as part of the definitions. -/
namespace OptimalG.Certificates.Transport

structure ReferenceNode where
  z : ℚ
  r : ℚ
  a : ℚ
  deriving DecidableEq,Repr

structure ReferenceSegment where
  left : ReferenceNode
  right : ReferenceNode
  deriving DecidableEq,Repr

namespace ReferenceSegment

def slope (seg : ReferenceSegment) (rank : ReferenceNode → ℚ) : ℚ :=
  (rank seg.right-rank seg.left)/(seg.right.z-seg.left.z)

noncomputable def rankMap (seg : ReferenceSegment) (rank : ReferenceNode → ℚ) (z : ℝ) : ℝ :=
  (rank seg.left:ℝ)+(seg.slope rank:ℝ)*(z-seg.left.z)

noncomputable def inverseRankMap (seg : ReferenceSegment) (rank : ReferenceNode → ℚ) (r : ℝ) : ℝ :=
  (seg.left.z:ℝ)+(r-rank seg.left)/(seg.slope rank:ℝ)

end ReferenceSegment

def referenceSegments : List ReferenceNode → List ReferenceSegment
  | a::b::rest => ⟨a,b⟩::referenceSegments (b::rest)
  | _ => []

end OptimalG.Certificates.Transport
