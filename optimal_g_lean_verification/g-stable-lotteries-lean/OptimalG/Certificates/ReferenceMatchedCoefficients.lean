import OptimalG.Certificates.ReferenceMatchedDisplacement
import OptimalG.Certificates.ReferenceChordCoefficients
import OptimalG.Certificates.ReferenceActiveTerms
import OptimalG.Certificates.ReferenceFirstForceAssembly

/-! The global competitor coefficients are selected on the same checked time
partition as the reference ODE. At each cell they are precisely the endpoint
of the actual Hessian comparison chord, with the single matching map. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory RatExpr
open scoped BigOperators
namespace ReferenceScalarCell

theorem globalMatchedRank_measurable (c : ReferenceScalarCell) (useR : Bool)
    {G : ℝ→ℝ} (hG : Measurable G) : Measurable (c.globalMatchedRank useR G) := by
  unfold globalMatchedRank
  split_ifs
  · exact hG.comp (c.referenceRank_measurable useR)
  · exact c.referenceRank_measurable useR

theorem endpointChord_input_measurable (c : ReferenceScalarCell) (S : ℝ)
    {r a : ℝ→ℝ} (hr : Measurable r) (ha : Measurable a) (i : Fin 16) :
    Measurable (fun t=>c.endpointChord t (fun _=>0) S (r t) (a t) i) := by
  have hf (j : Fin 16) : Measurable (fun t=>c.frozenInput t j) :=
    (c.frozenSubstitution j).measurable_evalOne
  by_cases h0 : i=0
  · subst i
    convert (measurable_const : Measurable (fun _ : ℝ=>S)) using 1
    funext t
    exact (c.endpointChord_coordinates t (fun _=>0) S (r t) (a t)).1
  by_cases h1 : i=1
  · subst i
    convert hr using 1
    funext t
    exact (c.endpointChord_coordinates t (fun _=>0) S (r t) (a t)).2.1
  by_cases h2 : i=2
  · subst i
    convert ha using 1
    funext t
    exact (c.endpointChord_coordinates t (fun _=>0) S (r t) (a t)).2.2.1
  by_cases hlo : i.val<12
  · have hthree : (3 : ℕ) ≤ i.val := by omega
    convert hf i using 1
    funext t
    exact (c.endpointChord_coordinates t (fun _=>0) S (r t) (a t)).2.2.2 i hthree hlo
  · have he : (fun t=>c.endpointChord t (fun _=>0) S (r t) (a t) i)=(fun _ : ℝ=>0) := by
      funext t
      fin_cases i <;> simp_all [endpointChord,FrozenParameters.comparisonChord,
        FrozenParameters.threeDirection,weightedInput]
    rw [he]
    exact measurable_const

theorem endpointChord_coefficient_weights (c : ReferenceScalarCell) (t S r a : ℝ)
    (w v : Fin 4→ℝ) (i : Fin 4) :
    (c.params.coefficients c.flow.late i).eval (c.endpointChord t w S r a)=
      (c.params.coefficients c.flow.late i).eval (c.endpointChord t v S r a) := by
  rw [endpointChord_coefficient,endpointChord_coefficient]

end ReferenceScalarCell

noncomputable def referenceMatchedCoefficient
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell) (cells : List ReferenceFlowCell)
    (S : ℝ) (G : ℝ→ℝ) (i : Fin 4) : ℝ→ℝ :=
  referenceField (fun f t=>
    let c := scalarFor f
    (c.params.coefficients c.flow.late i).eval (c.endpointChord t (fun _=>0) S
      (c.globalMatchedRank true G t) (c.globalMatchedRank false G t))) cells

theorem referenceMatchedCoefficient_measurable
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell) (cells : List ReferenceFlowCell)
    (S : ℝ) {G : ℝ→ℝ} (hG : Measurable G) (i : Fin 4) :
    Measurable (referenceMatchedCoefficient scalarFor cells S G i) := by
  apply referenceField_measurable
  intro f
  exact RatExpr.measurable_eval (fun j=>(scalarFor f).endpointChord_input_measurable S
    ((scalarFor f).globalMatchedRank_measurable true hG)
    ((scalarFor f).globalMatchedRank_measurable false hG) j) _

theorem referenceMatchedCoefficient_on_cell
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    {start finish : ℚ} {cells : List ReferenceFlowCell} {c : ReferenceScalarCell}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : c.flow∈cells)
    (hcell : scalarFor c.flow=c) (S : ℝ) (G : ℝ→ℝ) {z : ℝ}
    (hz : z∈Ioc (c.flow.segment.left.z:ℝ) c.flow.segment.right.z)
    (w : Fin 4→ℝ) (i : Fin 4) :
    referenceMatchedCoefficient scalarFor cells S G i z=
      (c.params.coefficients c.flow.late i).eval
        (c.endpointChord (c.flow.timeParameter z) w S
          (c.globalMatchedRank true G (c.flow.timeParameter z))
          (c.globalMatchedRank false G (c.flow.timeParameter z))) := by
  rw [referenceMatchedCoefficient,referenceField_on_cell _ hcover hmem hz,hcell]
  exact c.endpointChord_coefficient_weights _ _ _ _ _ _ i

theorem referenceMatched_source_on_cell
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    {start finish : ℚ} {cells : List ReferenceFlowCell} {c : ReferenceScalarCell}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : c.flow∈cells)
    (hcell : scalarFor c.flow=c) (S : ℝ) (G rho Z : ℝ→ℝ) {z : ℝ}
    (hz : z∈Ioc (c.flow.segment.left.z:ℝ) c.flow.segment.right.z)
    (w : Fin 4→ℝ)
    (hw : ∀ i,w i=rho z*Variational.referenceWeight (referenceCoefficient cells i z)
      (Variational.transportDelta i) (Real.log (Z z))) :
    Variational.transportCoefficientSource rho (fun t=>Real.log (Z t))
      (fun t i=>referenceMatchedCoefficient scalarFor cells S G i t)
      (fun t i=>referenceCoefficient cells i t) Variational.transportDelta z=
      ∑ i∈FrozenParameters.activeTerms c.flow.late,w i*Real.log
        ((c.params.coefficients c.flow.late i).eval
          (c.endpointChord (c.flow.timeParameter z) w S
            (c.globalMatchedRank true G (c.flow.timeParameter z))
            (c.globalMatchedRank false G (c.flow.timeParameter z)))/
          (c.params.coefficients c.flow.late i).eval
            (c.weightedInput (c.flow.timeParameter z) w)) := by
  rw [FrozenParameters.transportCoefficientSource_eq_active (late := c.flow.late) hw (by
    intro he
    rw [referenceCoefficient_on_cell_frozen hcover hmem hz 0,
      referenceCoefficient_on_cell_frozen hcover hmem hz 2,he]
    simp [FrozenParameters.coefficients,FrozenParameters.numerators,eval_mulNotation,
      eval_divNotation,eval])]
  apply Finset.sum_congr rfl
  intro i hi
  rw [referenceMatchedCoefficient_on_cell scalarFor hcover hmem hcell S G hz w i,
    referenceCoefficient_on_cell_frozen hcover hmem hz i,c.weightedInput_coefficient]

end OptimalG.Certificates.Transport
