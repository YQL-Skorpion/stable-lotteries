import OptimalG.Certificates.ReferenceMatchedDerivative
import OptimalG.VariationalTransportAllocation

/-! The four genuine logarithmic weights push forward to the same rank
density W for both the linear derivative term and the entropy term. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory Variational

theorem four_weighted_rank_test (weight : Fin 4→ℝ) (F : ℝ→ℝ) (xiR xiA : ℝ) :
    (∑ i,weight i*F (transportXi xiR xiA i))=
      (weight 0+weight 2)*F xiR+(weight 1+weight 3)*F xiA := by
  simp [Fin.sum_univ_succ,transportXi]
  ring

/-- A generic test is instantiated with `xi-1` or `transportEntropy xi`.
The actual local crop relation is supplied by the previous module, and the
finite interval bounds supply all integrability premises. -/
theorem reference_weighted_test_integral
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    (coarse : List ReferenceFlowCell) (G F : ℝ→ℝ) (weight : Fin 4→ℝ→ℝ)
    {start finish : ℚ} {cells : List ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish cells=true) (a b : ℝ)
    (hrankR : ∀ c∈cells,(c.segment.left.r:ℝ)<c.segment.right.r)
    (hrankA : ∀ c∈cells,(c.segment.left.a:ℝ)<c.segment.right.a)
    (hlocalR : ∀ c∈cells,∀ z∈Ioo (c.segment.left.z:ℝ) c.segment.right.z,
      F (referenceDerivative scalarFor coarse true G z)=
        (Icc a b).indicator (fun r=>F (deriv G r)) (c.segment.rankMap (·.r) z))
    (hlocalA : ∀ c∈cells,∀ z∈Ioo (c.segment.left.z:ℝ) c.segment.right.z,
      F (referenceDerivative scalarFor coarse false G z)=
        (Icc a b).indicator (fun r=>F (deriv G r)) (c.segment.rankMap (·.a) z))
    (htimeR : ∀ c∈cells,IntervalIntegrable
      (fun z=>F (referenceDerivative scalarFor coarse true G z)*(weight 0 z+weight 2 z))
      volume (c.segment.left.z:ℝ) c.segment.right.z)
    (htimeA : ∀ c∈cells,IntervalIntegrable
      (fun z=>F (referenceDerivative scalarFor coarse false G z)*(weight 1 z+weight 3 z))
      volume (c.segment.left.z:ℝ) c.segment.right.z)
    (hdensityR : ∀ c∈cells,Integrable (fun r=>segmentDensity c.segment (·.r)
      (fun z=>weight 0 z+weight 2 z) r*(Icc a b).indicator (fun r=>F (deriv G r)) r))
    (hdensityA : ∀ c∈cells,Integrable (fun r=>segmentDensity c.segment (·.a)
      (fun z=>weight 1 z+weight 3 z) r*(Icc a b).indicator (fun r=>F (deriv G r)) r)) :
    (∫ z in (start:ℝ)..finish,∑ i,weight i z*F (referenceXi scalarFor coarse G z i))=
      ∫ r in Icc a b,W (cells.map (·.segment))
        (fun _ z=>weight 0 z+weight 2 z) (fun _ z=>weight 1 z+weight 3 z) r*
          F (deriv G r) := by
  have he := reference_two_positional_pushforwards hc
    (fun z=>F (referenceDerivative scalarFor coarse true G z))
    (fun z=>F (referenceDerivative scalarFor coarse false G z))
    (fun z=>weight 0 z+weight 2 z) (fun z=>weight 1 z+weight 3 z)
    (fun r=>F (deriv G r)) a b hrankR hrankA hlocalR hlocalA
    htimeR htimeA hdensityR hdensityA
  change _=∫ r in Icc a b,f (cells.map (·.segment))
    (fun _ z=>weight 0 z+weight 2 z) (fun _ z=>weight 1 z+weight 3 z) r*F (deriv G r)
  rw [←he]
  apply intervalIntegral.integral_congr
  intro z hz
  dsimp only [referenceXi]
  rw [four_weighted_rank_test]
  ring

theorem genuine_weighted_test_eq (rho w0 : ℝ→ℝ) (coeff0 : ℝ→Fin 4→ℝ)
    (weight : Fin 4→ℝ→ℝ) (xi : ℝ→Fin 4→ℝ) (F : ℝ→ℝ) {z : ℝ}
    (hw : ∀ i,weight i z=rho z*referenceWeight (coeff0 z i) (transportDelta i) (w0 z)) :
    rho z*(∑ i,referenceWeight (coeff0 z i) (transportDelta i) (w0 z)*F (xi z i))=
      ∑ i,weight i z*F (xi z i) := by
  simp only [hw,Finset.mul_sum,mul_assoc]

theorem genuine_derivative_source_eq (rho w0 : ℝ→ℝ) (coeff0 : ℝ→Fin 4→ℝ)
    (weight : Fin 4→ℝ→ℝ) (xi : ℝ→Fin 4→ℝ) {z : ℝ}
    (hw : ∀ i,weight i z=rho z*referenceWeight (coeff0 z i) (transportDelta i) (w0 z)) :
    transportDerivativeSource rho w0 coeff0 xi transportDelta z=
      ∑ i,weight i z*(xi z i-1) :=
  genuine_weighted_test_eq rho w0 coeff0 weight xi (·-1) hw

theorem genuine_entropy_source_eq (rho w0 : ℝ→ℝ) (coeff0 : ℝ→Fin 4→ℝ)
    (weight : Fin 4→ℝ→ℝ) (xi : ℝ→Fin 4→ℝ) {z : ℝ}
    (hw : ∀ i,weight i z=rho z*referenceWeight (coeff0 z i) (transportDelta i) (w0 z)) :
    transportEntropySource rho w0 coeff0 xi transportDelta z=
      ∑ i,weight i z*transportEntropy (xi z i) :=
  genuine_weighted_test_eq rho w0 coeff0 weight xi transportEntropy hw

end OptimalG.Certificates.Transport
