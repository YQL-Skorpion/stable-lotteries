import OptimalG.Certificates.StaticControlsVerified
import OptimalG.Certificates.StaticAllMass
import OptimalG.StableExistence

/-! The explicit rational activation and its universal finite-election upper
bound. This file is independent of the lower exclusion certificate. -/
namespace OptimalG
open Set Certificates

noncomputable def certifiedActivation : ℝ→ℝ := normalizedActivation StaticCurve.score

theorem certifiedActivation_admissible : AdmissibleActivation certifiedActivation := by
  refine ⟨normalizedActivation_continuousOn StaticCurve.verifierCurve.continuous,?_⟩
  intro r hr
  exact normalizedActivation_mem_Icc StaticCurve.verifierCurve.decreasing
    StaticCurve.verifierCurve.at_one hr

theorem certified_upper_212466 : UniversalBound certifiedActivation (106233/50000) := by
  exact StaticCurve.universal_upper_of_supported_controls StaticCurve.supported_controls

theorem certifiedActivation_stable_exists (E : Election) :
    ∃ D : Lottery E.candidateCount,E.Stable certifiedActivation D :=
  E.exists_stable certifiedActivation certifiedActivation_admissible.1

end OptimalG
