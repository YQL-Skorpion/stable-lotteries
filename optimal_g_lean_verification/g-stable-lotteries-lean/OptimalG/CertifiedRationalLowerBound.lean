import OptimalG.RationalLowerBound
import OptimalG.UniversalLPVerifiedBounds
import OptimalG.Certificates.ReferenceFlowData.CoarseLowerShape

/-! The fixed lower endpoint 2.12465, with the actual finite-election and
positive-cost metric-witness semantics. Only the lower reference branch is
imported; no minimizing curve or upper construction occurs in this proof. -/
namespace OptimalG
open Set Variational Certificates ParameterTransfer

 theorem certified_parameter_lower_endpoint_excluded : ¬Feasible (22493/40000) := by
  have h := ReferenceFlowData.CoarseLowerShape.lower_endpoint_not_feasible
  norm_num [TransportReferenceData.CoarseLowerShape.data,
    TransportReferenceData.CoarseLowerShape.lam] at h ⊢
  exact h

 theorem certified_witness_above_212465 (g : ℝ→ℝ)
    (hg : ContinuousOn g (Icc 0 1)) : WitnessAbove g (42493/20000) :=
  witness_212465_of_endpoint_exclusion
    (fun _ hn => hn.universal_lp_primitive_bounds (by constructor <;> norm_num))
    certified_parameter_lower_endpoint_excluded g hg

 theorem certified_maximumDistortion_ge_212465 (g : ℝ→ℝ)
    (hg : AdmissibleActivation g) :
    ENNReal.ofReal (42493/20000:ℝ)≤maximumDistortion g :=
  witnessAbove_le_maximumDistortion g _ (certified_witness_above_212465 g hg.1)

end OptimalG
