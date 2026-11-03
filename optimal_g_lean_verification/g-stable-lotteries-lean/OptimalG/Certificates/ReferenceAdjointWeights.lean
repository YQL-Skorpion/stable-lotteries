import OptimalG.Certificates.ReferenceRefinedWeights
import OptimalG.VariationalReferenceWeightIdentity
import OptimalG.VariationalReferenceTerms

/-! The checked integer weight intervals enclose the actual logarithmic
adjoint weights of the same coarse reference ODE. Refinement preserves every
coefficient; the exponential representation is derived from the genuine flow.
-/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

namespace ReferenceFlowCell

theorem refinement_base_coefficient {parent child : ReferenceFlowCell} {lo hi : ℚ}
    (hc : parent.refinementCheck child lo hi=true) (i : Fin 4) (t : ℝ) :
    (child.baseCoefficientExpr i).evalOne t=
      (parent.baseCoefficientExpr i).evalOne ((lo:ℝ)+(hi-lo)*t) := by
  have h : child.lam=parent.lam ∧ child.slack=parent.slack ∧ child.level=parent.level ∧
      child.late=parent.late ∧ child.rPiece=parent.rPiece ∧ child.aPiece=parent.aPiece ∧
      child.segment.left=parent.interpolateNode lo ∧ child.segment.right=parent.interpolateNode hi ∧
      0≤lo ∧ lo<hi ∧ hi≤1 := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
  rcases h with ⟨hl,hs,hm,hb,hrp,hap,_,_,_,_,_⟩
  have hf := refinementCheck_fields hc t
  rw [baseCoefficientExpr_eval,baseCoefficientExpr_eval]
  have hp : child.frozenParameters=parent.frozenParameters := by
    simp only [frozenParameters,hl,hs,hm]
  rw [hp,hb]
  apply FrozenParameters.coefficients_reference_invariant
  all_goals simp [baseInput,baseSubstitution,RatExpr.evalOne,RatExpr.eval,
    Rexpr,scoreR,scoreA,primitiveExpr_eval,scoreExpr_eval,frozenParameters,hl,hs,hm,hrp,hap,
    show child.rankR.eval (fun _=>t)=parent.rankR.eval (fun _=>((lo:ℝ)+(hi-lo)*t)) from hf.1,
    show child.rankA.eval (fun _=>t)=parent.rankA.eval (fun _=>((lo:ℝ)+(hi-lo)*t)) from hf.2.1,
    show child.highRank.eval (fun _=>t)=parent.highRank.eval (fun _=>((lo:ℝ)+(hi-lo)*t)) from hf.2.2.1]

end ReferenceFlowCell

noncomputable def referenceCoefficient (cells : List ReferenceFlowCell) (i : Fin 4) : ℝ→ℝ :=
  referenceField (fun c t=>(c.baseCoefficientExpr i).evalOne t) cells

theorem referenceCoefficient_measurable (cells : List ReferenceFlowCell) (i : Fin 4) :
    Measurable (referenceCoefficient cells i) :=
  referenceField_measurable _ (fun c=>(c.baseCoefficientExpr i).measurable_evalOne) cells

theorem referenceCoefficient_on_refined_cell {start finish lo hi : ℚ}
    {cells : List ReferenceFlowCell} {parent child : ReferenceFlowCell}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : parent∈cells)
    (href : parent.refinementCheck child lo hi=true) {z : ℝ}
    (hz : z∈Ioc (child.segment.left.z:ℝ) child.segment.right.z) (i : Fin 4) :
    referenceCoefficient cells i z=(child.baseCoefficientExpr i).evalOne (child.timeParameter z) := by
  have hp := (referenceFlowCoverCheck_bounds hcover hmem).2.1
  have hzp := ReferenceFlowCell.refinement_mem_parent href hp hz
  have ht := (ReferenceFlowCell.refinement_time_geometry href hp).2.2.2 z
  rw [referenceCoefficient,referenceField_on_cell _ hcover hmem hzp,ht]
  exact (ReferenceFlowCell.refinement_base_coefficient href i _).symm

theorem checked_refined_adjoint_weights {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceWeightCertificate) (hc : c.check s k=true)
    {start finish lo hi L S : ℚ} {cells : List ReferenceFlowCell} {parent : ReferenceFlowCell}
    {pieces : List CubicPiece}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : parent∈cells)
    (href : parent.refinementCheck c.cell.flow lo hi=true) (hstart : c.start=start)
    (hcurve : trajectoryCheck L S pieces=true)
    (hpiece : parent.canonicalPiece∈pieces) (hpoly : parent.canonicalPieceCheck=true)
    {Z : ℝ→ℝ}
    (herror : ∀ z∈Icc (start:ℝ) finish,
      |Z z-cubicPrimitive L S pieces z|≤(z-start)/2500000000)
    (ha : IntervalIntegrable (referenceField ReferenceFlowCell.actualAlpha cells) volume
      (start:ℝ) finish)
    (hb : IntervalIntegrable (referenceField ReferenceFlowCell.actualBeta cells) volume
      (start:ℝ) finish)
    (hZ : AbsolutelyContinuousOnInterval Z start finish)
    (hpositive : ∀ z∈Icc (start:ℝ) finish,0<Z z)
    (hder : ∀ᵐ z ∂volume.restrict (Icc (start:ℝ) finish),
      deriv Z z=referenceField ReferenceFlowCell.actualAlpha cells z*Z z+
        referenceField ReferenceFlowCell.actualBeta cells z)
    {z : ℝ} (hz : z∈Ioc (c.cell.flow.segment.left.z:ℝ) c.cell.flow.segment.right.z)
    (he : c.cell.exponent.Contains s
      (∫ x in z..(finish:ℝ),referenceField ReferenceFlowCell.actualAlpha cells x))
    (hT : c.cell.terminal.Contains s (Z finish)) (i : Fin 4) :
    (c.cell.weights i).Contains s
      (Variational.referenceIntegratingFactor start finish
        (fun t=>referenceField ReferenceFlowCell.actualBeta cells t/Z t) z*
       Variational.referenceWeight (referenceCoefficient cells i z)
        (Variational.transportDelta i) (Real.log (Z z))) := by
  have hp := referenceFlowCoverCheck_bounds hcover hmem
  have hg := ReferenceFlowCell.refinement_time_geometry href hp.2.1
  have hwhole : z∈Icc (start:ℝ) finish :=
    ⟨(show (start:ℝ)≤c.cell.flow.segment.left.z by exact_mod_cast hp.1.trans hg.2.1).trans hz.1.le,
      hz.2.trans (by exact_mod_cast hg.2.2.1.trans hp.2.2)⟩
  have horder : (start:ℝ)≤finish := by
    exact_mod_cast referenceFlowCoverCheck_order hcover
  have hweight := checked_refined_actual_weights hs hk c hc hcover hmem href hstart
    hcurve hpiece hpoly herror ⟨hz.1.le,hz.2⟩ he hT i
  rw [Variational.affine_solution_adjoint_at horder ha hb hZ hpositive hder hwhole,
    Variational.reference_weight_power (hpositive z hwhole) i,
    referenceCoefficient_on_refined_cell hcover hmem href hz i]
  convert hweight using 1 <;> split_ifs <;> first | omega | ring

end OptimalG.Certificates.Transport
