import OptimalG.Certificates.ReferenceMatchedGlobal
import OptimalG.Certificates.ReferenceFlowPartition
import OptimalG.VariationalTransportLocalization

/-! Actual rank displacements use the single Stieltjes matching on central
reference pieces and vanish on the fixed cap pieces. They are measurable,
bounded, and obey the matching variation estimate on the full time interval. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory
namespace ReferenceScalarCell

noncomputable def matchedDisplacement (c : ReferenceScalarCell) (useR : Bool)
    (G : ℝ→ℝ) (t : ℝ) : ℝ := c.globalMatchedRank useR G t-c.referenceRank useR t

theorem referenceRank_measurable (c : ReferenceScalarCell) (useR : Bool) :
    Measurable (c.referenceRank useR) := by
  cases useR
  · exact c.flow.rankA.measurable_evalOne
  · exact c.flow.rankR.measurable_evalOne

theorem matchedDisplacement_measurable (c : ReferenceScalarCell) (useR : Bool)
    {G : ℝ→ℝ} (hG : Measurable G) : Measurable (c.matchedDisplacement useR G) := by
  unfold matchedDisplacement globalMatchedRank
  split_ifs
  · exact (hG.comp (c.referenceRank_measurable useR)).sub (c.referenceRank_measurable useR)
  · exact (c.referenceRank_measurable useR).sub (c.referenceRank_measurable useR)

theorem matchedDisplacement_abs_le (c : ReferenceScalarCell) (useR : Bool)
    {G : ℝ→ℝ} {left right t : ℝ} (ho : left≤right)
    (hG : ∀ r∈Icc left right,G r∈Icc left right)
    (hr : (c.rankProfile useR ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).piece.isSome=true →
      c.referenceRank useR t∈Icc left right) :
    |c.matchedDisplacement useR G t|≤right-left := by
  unfold matchedDisplacement globalMatchedRank
  split_ifs with hp
  · have hh := hr hp
    have hg := hG _ hh
    apply abs_le.mpr
    constructor <;> linarith [hh.1,hh.2,hg.1,hg.2]
  · simp only [sub_self,abs_zero]
    exact sub_nonneg.mpr ho

theorem matchedDisplacement_sq_le (c : ReferenceScalarCell) (useR : Bool)
    {G : ℝ→ℝ} {left right t B : ℝ} (hB : 0≤B)
    (hG : ∀ r∈Icc left right,(G r-r)^2≤B)
    (hr : (c.rankProfile useR ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).piece.isSome=true →
      c.referenceRank useR t∈Icc left right) :
    (c.matchedDisplacement useR G t)^2≤B := by
  unfold matchedDisplacement globalMatchedRank
  split_ifs with hp
  · exact hG _ (hr hp)
  · simpa only [sub_self,zero_pow (by decide : 2≠0)] using hB

end ReferenceScalarCell

noncomputable def referenceDisplacement
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell) (cells : List ReferenceFlowCell)
    (useR : Bool) (G : ℝ→ℝ) : ℝ→ℝ :=
  referenceField (fun c=>(scalarFor c).matchedDisplacement useR G) cells

theorem referenceDisplacement_measurable
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell) (cells : List ReferenceFlowCell)
    (useR : Bool) {G : ℝ→ℝ} (hG : Measurable G) :
    Measurable (referenceDisplacement scalarFor cells useR G) :=
  referenceField_measurable _ (fun c=>(scalarFor c).matchedDisplacement_measurable useR hG) _

theorem referenceDisplacement_on_cell
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    {start finish : ℚ} {cells : List ReferenceFlowCell} {c : ReferenceScalarCell}
    (hc : referenceFlowCoverCheck start finish cells=true) (hm : c.flow∈cells)
    (hcell : scalarFor c.flow=c) (useR : Bool) (G : ℝ→ℝ) {z : ℝ}
    (hz : z∈Ioc (c.flow.segment.left.z:ℝ) c.flow.segment.right.z) :
    referenceDisplacement scalarFor cells useR G z=
      c.matchedDisplacement useR G (c.flow.timeParameter z) := by
  rw [referenceDisplacement,referenceField_on_cell _ hc hm hz,hcell]

theorem referenceDisplacement_bounds
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    {start finish : ℚ} {cells : List ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish cells=true) (useR : Bool)
    {left right : ℝ} (ho : left≤right) (G : StieltjesFunction ℝ)
    (hG : ∀ r∈Icc left right,G r∈Icc left right)
    (hsq : ∀ r∈Icc left right,(G r-r)^2≤
      2*(right-left)*Variational.matchingVariation G left right)
    (hshape : ∀ c∈cells,∀ t∈Icc (0:ℝ) 1,
      ((scalarFor c).rankProfile useR ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).piece.isSome=true →
        (scalarFor c).referenceRank useR t∈Icc left right)
    {z : ℝ} (hz : z∈Ioc (start:ℝ) finish) :
    |referenceDisplacement scalarFor cells useR G z|≤right-left ∧
      (referenceDisplacement scalarFor cells useR G z)^2≤
        2*(right-left)*Variational.matchingVariation G left right := by
  obtain ⟨c,hm,hord,hzc,he⟩ := referenceField_selected
    (fun c=>(scalarFor c).matchedDisplacement useR G) hc hz
  change |referenceField _ cells z|≤_ ∧ (referenceField _ cells z)^2≤_
  rw [he]
  have ht := c.timeParameter_mem hord ⟨hzc.1.le,hzc.2⟩
  exact ⟨(scalarFor c).matchedDisplacement_abs_le useR ho hG (hshape c hm _ ht),
    (scalarFor c).matchedDisplacement_sq_le useR
      (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr ho))
        (Variational.matchingVariation_nonneg G left right)) hsq (hshape c hm _ ht)⟩

end OptimalG.Certificates.Transport
