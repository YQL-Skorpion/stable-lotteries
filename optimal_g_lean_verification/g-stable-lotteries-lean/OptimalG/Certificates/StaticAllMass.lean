import OptimalG.Certificates.StaticLowMass
import OptimalG.Certificates.StaticVariationalMass
import OptimalG.Certificates.StaticExtendedMass
import OptimalG.Certificates.StaticHighMass
import OptimalG.VerifierChoice
import OptimalG.FiniteVerifier
import OptimalG.Certificates.StaticBinaryVerified

/-! The fixed candidate's final sufficient-verifier assembly. The two explicit
inputs are discharged by the separate high-control and binary certificates. -/
namespace OptimalG.Certificates.StaticCurve
open Set Variational

theorem all_mass_verifier
    (hcontrol : ∀ r∈Icc zStart 1,∀ v∈controlFeatureSupport staticLowData,
      score r≤featureH staticLow_admissible r (curvePrimitive score r) v)
    (hbinary : ∀ p∈Ioo (StaticLow.lam:ℝ) 1,∀ q∈Icc (0:ℝ) StaticLow.lam,
      q+(p/curvePrimitive score p)*packingDelta score p q≤StaticLow.lam) :
    ∃ beta corr,VerifierOn (Ioo (0:ℝ) 1) score StaticLow.lam beta corr := by
  apply exists_verifier_of_singletons
  intro p hp
  by_cases hpl : p≤(StaticLow.lam:ℝ)
  · have htest : ∃ b e,ThreeFunctionTest score StaticLow.lam p b e := by
      by_cases hl : p≤527/2000
      · exact low_mass hcontrol ⟨hp.1,hl⟩
      by_cases hm : p≤9/25
      · exact variational_mass hcontrol ⟨(lt_of_not_ge hl).le,hm⟩
      · exact extended_mass hcontrol ⟨(lt_of_not_ge hm).le,hpl⟩
    obtain ⟨b,e,he⟩ := htest
    exact ⟨b,fun x=>correction StaticLow.lam e x (score x),
      threeFunctionTest_verifier verifierCurve hp.1 hpl he⟩
  · have hh := high_mass hcontrol hbinary
    refine ⟨p/curvePrimitive score p,highMassCorrection score StaticLow.lam p,
      hh.transport ?_ ?_ ?_⟩
    · intro x hx
      have hx' : x=p := hx
      subst x
      exact ⟨lt_of_not_ge hpl,hp.2⟩
    · intro x hx
      have hx' : x=p := hx
      subst x
      rfl
    · intro x hx r hr
      have hx' : x=p := hx
      subst x
      rfl

theorem universal_upper_of_control_and_binary
    (hcontrol : ∀ r∈Icc zStart 1,∀ v∈controlFeatureSupport staticLowData,
      score r≤featureH staticLow_admissible r (curvePrimitive score r) v)
    (hbinary : ∀ p∈Ioo (StaticLow.lam:ℝ) 1,∀ q∈Icc (0:ℝ) StaticLow.lam,
      q+(p/curvePrimitive score p)*packingDelta score p q≤StaticLow.lam) :
    UniversalBound (normalizedActivation score) (106233/50000) := by
  obtain ⟨beta,corr,hv⟩ := all_mass_verifier hcontrol hbinary
  convert verifier_universalBound verifierCurve beta corr hv using 1 <;>
    norm_num [StaticLow.lam]

/-- The actual static binary certificate discharges the last binary premise. -/
theorem universal_upper_of_supported_controls
    (hcontrol : ∀ r∈Icc zStart 1,∀ v∈controlFeatureSupport staticLowData,
      score r≤featureH staticLow_admissible r (curvePrimitive score r) v) :
    UniversalBound (normalizedActivation score) (106233/50000) := by
  apply universal_upper_of_control_and_binary hcontrol
  intro p hp q hq
  exact binary_of_supported_controls hcontrol p
    ⟨verifierCurve.lam_pos.trans hp.1,hp.2⟩ q ⟨hq.1,hq.2.trans hp.1.le⟩

end OptimalG.Certificates.StaticCurve
