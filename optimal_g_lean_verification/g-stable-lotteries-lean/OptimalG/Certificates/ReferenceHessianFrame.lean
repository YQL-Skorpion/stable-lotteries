import OptimalG.Certificates.ReferenceBaseCoefficients
import OptimalG.Certificates.ReferenceFrozenProfiles
import OptimalG.Certificates.ReferenceTimeBounds
import OptimalG.Certificates.ReferenceRankOrder
import OptimalG.Certificates.HessianChordBounds

/-! Assemble the fifteen actual frozen coordinates of a Hessian cell from
the independently checked low profiles, affine ranks, time warp and adjoint
weights. Only the first three coordinates change along a comparison chord.
-/
namespace OptimalG.Certificates.Transport.ReferenceScalarCell
open Set

noncomputable def weightedInput (c : ReferenceScalarCell) (t : ℝ) (w : Fin 4→ℝ) : Fin 16→ℝ :=
  ![c.frozenInput t 0,c.frozenInput t 1,c.frozenInput t 2,c.frozenInput t 3,
    c.frozenInput t 4,c.frozenInput t 5,c.frozenInput t 6,c.frozenInput t 7,
    c.frozenInput t 8,c.frozenInput t 9,c.frozenInput t 10,c.frozenInput t 11,
    w 0,w 1,w 2,w 3]

theorem checked_frozen_frame {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceScalarCell) (cell : HessianCell) (rb ab : ReferenceProfileBox)
    (hrProfile : (c.rProfile rb).check s k=true)
    (haProfile : (c.aProfile ab).check s k=true)
    (hrorder : c.flow.segment.left.r≤c.flow.segment.right.r)
    (haorder : c.flow.segment.left.a≤c.flow.segment.right.a)
    (hrank : IntegerInterval.rationalEndpointsCheck s c.flow.segment.left.r
      c.flow.segment.right.r (cell.fixed 0)=true)
    (haank : IntegerInterval.rationalEndpointsCheck s c.flow.segment.left.a
      c.flow.segment.right.a (cell.fixed 1)=true)
    (hrbox : rb.primitive=cell.fixed 2 ∧ rb.score=cell.fixed 6 ∧
      rb.gauge=cell.fixed 3 ∧ rb.gaugeDerivative=cell.fixed 7)
    (habox : ab.score=cell.fixed 8 ∧ ab.gaugeDerivative=cell.fixed 9)
    (htime : c.timeBoundsCheck s k (cell.fixed 4) (cell.fixed 5) (cell.fixed 10)=true)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ i,(cell.fixed ⟨11+i.val,by omega⟩).Contains s (w i)) :
    ∀ i,(cell.fixed i).Contains s (c.weightedInput t w i.succ) := by
  have hr := c.checked_rProfile_coordinates hs hk rb hrProfile hrorder ht
  have ha := c.checked_aProfile_coordinates hs hk ab haProfile haorder ht
  have htime' := c.checked_time_bounds hs hk _ _ _ htime ht
  have hR : (cell.fixed 0).Contains s (c.frozenInput t 1) := by
    exact IntegerInterval.rationalEndpointsCheck_sound hrank
      (ReferenceFlowCell.affineExpr_mem hrorder ht)
  have hA : (cell.fixed 1).Contains s (c.frozenInput t 2) := by
    exact IntegerInterval.rationalEndpointsCheck_sound haank
      (ReferenceFlowCell.affineExpr_mem haorder ht)
  rw [hrbox.1,hrbox.2.1,hrbox.2.2.1,hrbox.2.2.2] at hr
  rw [habox.1,habox.2] at ha
  intro i
  fin_cases i
  · simpa [weightedInput] using hR
  · simpa [weightedInput] using hA
  · simpa [weightedInput] using hr.1
  · simpa [weightedInput] using hr.2.2.1
  · simpa [weightedInput] using htime'.1
  · simpa [weightedInput] using htime'.2.1
  · simpa [weightedInput] using hr.2.1
  · simpa [weightedInput] using hr.2.2.2
  · simpa [weightedInput] using ha.1
  · simpa [weightedInput] using ha.2
  · simpa [weightedInput] using htime'.2.2
  · simpa [weightedInput] using hw 0
  · simpa [weightedInput] using hw 1
  · simpa [weightedInput] using hw 2
  · simpa [weightedInput] using hw 3

theorem weightedInput_coefficient (c : ReferenceScalarCell) (t : ℝ) (w : Fin 4→ℝ)
    (i : Fin 4) :
    (c.params.coefficients c.flow.late i).eval (c.weightedInput t w)=
      (c.params.coefficients c.flow.late i).eval (c.frozenInput t) := by
  apply FrozenParameters.coefficients_reference_invariant
  all_goals simp [weightedInput,frozenInput,frozenSubstitution,params,RatExpr.evalOne,RatExpr.eval]

end OptimalG.Certificates.Transport.ReferenceScalarCell
