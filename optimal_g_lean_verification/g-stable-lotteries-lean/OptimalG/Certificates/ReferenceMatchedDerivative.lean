import OptimalG.Certificates.ReferenceDisplacementCrop
import OptimalG.Certificates.ReferenceFlowAE
import OptimalG.VariationalStieltjesIntegrability
import OptimalG.VariationalReferencePullback
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! The reciprocal-derivative and entropy terms use one genuine matched
derivative field. Its value is G' on central profiles and 1 on fixed cap
profiles. All four coefficient terms use the allocation [r,a,r,a]. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory Variational
namespace ReferenceScalarCell

noncomputable def matchedDerivative (c : ReferenceScalarCell) (useR : Bool)
    (G : ℝ→ℝ) (t : ℝ) : ℝ :=
  if (c.rankProfile useR ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).piece.isSome
  then deriv G (c.referenceRank useR t) else 1

theorem matchedDerivative_measurable (c : ReferenceScalarCell) (useR : Bool)
    (G : ℝ→ℝ) : Measurable (c.matchedDerivative useR G) := by
  unfold matchedDerivative
  split_ifs
  · exact (measurable_deriv G).comp (c.referenceRank_measurable useR)
  · exact measurable_const

theorem matchedDerivative_test_displacement (c : ReferenceScalarCell) (useR : Bool)
    (G F : ℝ→ℝ) (hF : F 1=0) (t : ℝ) :
    F (c.matchedDerivative useR G t)=
      c.matchedDisplacement useR (fun r=>F (deriv G r)+r) t := by
  unfold matchedDerivative matchedDisplacement globalMatchedRank
  split_ifs <;> simp only [hF,add_sub_cancel_right,sub_self]

theorem matchedDerivative_refinement {parent child : ReferenceScalarCell} {lo hi : ℚ}
    (hc : parent.flow.refinementCheck child.flow lo hi=true)
    (useR : Bool) (G : ℝ→ℝ) (t : ℝ) :
    child.matchedDerivative useR G t=
      parent.matchedDerivative useR G ((lo:ℝ)+(hi-lo)*t) := by
  have hh := matchedDisplacement_refinement hc useR (fun r=>deriv G r-1+r) t
  rw [←child.matchedDerivative_test_displacement useR G (·-1) (by norm_num),
    ←parent.matchedDerivative_test_displacement useR G (·-1) (by norm_num)] at hh
  linarith only [hh]

end ReferenceScalarCell

noncomputable def referenceDerivative
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell) (cells : List ReferenceFlowCell)
    (useR : Bool) (G : ℝ→ℝ) : ℝ→ℝ :=
  referenceField (fun c=>(scalarFor c).matchedDerivative useR G) cells

noncomputable def referenceXi
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell) (cells : List ReferenceFlowCell)
    (G : ℝ→ℝ) (s : ℝ) : Fin 4→ℝ :=
  transportXi (referenceDerivative scalarFor cells true G s)
    (referenceDerivative scalarFor cells false G s)

theorem referenceDerivative_measurable
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell) (cells : List ReferenceFlowCell)
    (useR : Bool) (G : ℝ→ℝ) : Measurable (referenceDerivative scalarFor cells useR G) :=
  referenceField_measurable _ (fun c=>(scalarFor c).matchedDerivative_measurable useR G) _

theorem referenceDerivative_ae_lower
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    (hscalar : ∀ f,(scalarFor f).flow=f)
    {start finish : ℚ} {coarse : List ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish coarse=true)
    (useR : Bool) (G : ℝ→ℝ) {a b delta : ℝ} (hd : delta≤1)
    (hG : ∀ᵐ r ∂volume.restrict (Icc a b),delta≤deriv G r)
    (hrank : ∀ c∈coarse,
      (((if useR then (·.r) else (·.a)) c.segment.left):ℝ)<
        ((if useR then (·.r) else (·.a)) c.segment.right:ℚ))
    (himage : ∀ c∈coarse,((scalarFor c).rankProfile useR
      ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).piece.isSome=true →
      Icc (((if useR then (·.r) else (·.a)) c.segment.left):ℝ)
        ((if useR then (·.r) else (·.a)) c.segment.right:ℚ) ⊆ Icc a b) :
    ∀ᵐ z ∂volume.restrict (Icc (start:ℝ) finish),
      delta≤referenceDerivative scalarFor coarse useR G z := by
  rw [←Measure.restrict_congr_set Ioc_ae_eq_Icc]
  apply referenceFlowCoverCheck_ae_Ioc hc
  intro c hm
  by_cases hp : ((scalarFor c).rankProfile useR
      ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).piece.isSome=true
  · have ht : (c.segment.left.z:ℝ)<c.segment.right.z := by
      exact_mod_cast (referenceFlowCoverCheck_bounds hc hm).2.1
    have hg := ae_reference_segment_pullback c.segment
      (if useR then (·.r) else (·.a)) ht
      (by cases useR <;> simpa using hrank c hm)
      (by cases useR <;> simpa using himage c hm hp) hG
    rw [←Measure.restrict_congr_set Ioc_ae_eq_Icc] at hg
    filter_upwards [hg,ae_restrict_mem measurableSet_Ioc] with z hz hzi
    change delta≤referenceField _ coarse z
    rw [referenceField_on_cell _ hc hm hzi]
    simp only [ReferenceScalarCell.matchedDerivative,if_pos hp]
    have he := (scalarFor c).referenceRank_timeParameter useR z
    rw [hscalar] at he
    simpa only [he] using hz
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hzi
    change delta≤referenceField _ coarse z
    rw [referenceField_on_cell _ hc hm hzi]
    simpa only [ReferenceScalarCell.matchedDerivative,if_neg hp] using hd

theorem referenceXi_ae_positive
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell) (coarse : List ReferenceFlowCell)
    (G : ℝ→ℝ) {mu : Measure ℝ}
    (hR : ∀ᵐ z ∂mu,0<referenceDerivative scalarFor coarse true G z)
    (hA : ∀ᵐ z ∂mu,0<referenceDerivative scalarFor coarse false G z) :
    ∀ᵐ z ∂mu,∀ i,0<referenceXi scalarFor coarse G z i := by
  filter_upwards [hR,hA] with z hzR hzA
  intro i
  fin_cases i <;> simp_all [referenceXi, transportXi]

theorem referenceDerivative_on_refined_cell
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    (hscalar : ∀ f,(scalarFor f).flow=f)
    {start finish lo hi : ℚ} {coarse : List ReferenceFlowCell}
    {parent child : ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish coarse=true) (hm : parent∈coarse)
    (href : parent.refinementCheck child lo hi=true) (useR : Bool) (G : ℝ→ℝ) {z : ℝ}
    (hz : z∈Ioc (child.segment.left.z:ℝ) child.segment.right.z) :
    referenceDerivative scalarFor coarse useR G z=
      (scalarFor child).matchedDerivative useR G (child.timeParameter z) := by
  have hp := (referenceFlowCoverCheck_bounds hc hm).2.1
  have hzparent := ReferenceFlowCell.refinement_mem_parent href hp hz
  have ht := (ReferenceFlowCell.refinement_time_geometry href hp).2.2.2 z
  have href' : (scalarFor parent).flow.refinementCheck (scalarFor child).flow lo hi=true := by
    simpa only [hscalar] using href
  unfold referenceDerivative
  rw [referenceField_on_cell _ hc hm hzparent,ht]
  exact (ReferenceScalarCell.matchedDerivative_refinement href' useR G _).symm

theorem referenceDerivative_refined_test_of_frame
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    (hscalar : ∀ f,(scalarFor f).flow=f)
    {start finish lo hi : ℚ} {coarse : List ReferenceFlowCell}
    {parent child : ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish coarse=true) (hm : parent∈coarse)
    (href : parent.refinementCheck child lo hi=true) (ref : ReferenceData)
    (useR : Bool) (G F : ℝ→ℝ) (hF : F 1=0)
    (hframe : ((scalarFor child).rankProfile useR
      ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).frameCheck ref=true)
    (hr : (((if useR then (·.r) else (·.a)) child.segment.left):ℝ)<
      ((if useR then (·.r) else (·.a)) child.segment.right:ℚ))
    {z : ℝ} (hz : z∈Ioo (child.segment.left.z:ℝ) child.segment.right.z) :
    F (referenceDerivative scalarFor coarse useR G z)=
      (Icc (ref.leftContact:ℝ) ref.rightContact).indicator (fun r=>F (deriv G r))
        (child.segment.rankMap (if useR then (·.r) else (·.a)) z) := by
  rw [referenceDerivative_on_refined_cell scalarFor hscalar hc hm href useR G
    ⟨hz.1,hz.2.le⟩,(scalarFor child).matchedDerivative_test_displacement useR G F hF]
  rw [←referenceDisplacement_on_refined_cell scalarFor hscalar hc hm href useR
    (fun r=>F (deriv G r)+r) ⟨hz.1,hz.2.le⟩]
  simpa only [add_sub_cancel_right] using
    referenceDisplacement_refined_crop_of_frame scalarFor hscalar hc hm href ref useR
      (fun r=>F (deriv G r)+r) hframe hr hz

theorem referenceDerivative_refined_test
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    (hscalar : ∀ f,(scalarFor f).flow=f)
    {start finish lo hi : ℚ} {coarse : List ReferenceFlowCell}
    {parent child : ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish coarse=true) (hm : parent∈coarse)
    (href : parent.refinementCheck child lo hi=true)
    (useR : Bool) (G F : ℝ→ℝ) (hF : F 1=0)
    {a b z : ℝ} (hz : z∈Ioc (child.segment.left.z:ℝ) child.segment.right.z)
    (hcentral : ((scalarFor child).rankProfile useR
      ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).piece.isSome=true →
      child.segment.rankMap (if useR then (·.r) else (·.a)) z∈Icc a b)
    (hcap : ((scalarFor child).rankProfile useR
      ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).piece.isSome=false →
      child.segment.rankMap (if useR then (·.r) else (·.a)) z∉Icc a b) :
    F (referenceDerivative scalarFor coarse useR G z)=
      (Icc a b).indicator (fun r=>F (deriv G r))
        (child.segment.rankMap (if useR then (·.r) else (·.a)) z) := by
  rw [referenceDerivative_on_refined_cell scalarFor hscalar hc hm href useR G hz,
    (scalarFor child).matchedDerivative_test_displacement useR G F hF]
  rw [←referenceDisplacement_on_refined_cell scalarFor hscalar hc hm href useR
    (fun r=>F (deriv G r)+r) hz]
  simpa only [add_sub_cancel_right] using
    referenceDisplacement_refined_crop scalarFor hscalar hc hm href useR
      (fun r=>F (deriv G r)+r) hz hcentral hcap

end OptimalG.Certificates.Transport
