import OptimalG.Certificates.StaticCurve
import OptimalG.Certificates.StaticLowAdmissible
import OptimalG.Certificates.StaticContactGeometry
import OptimalG.VariationalTerminalControl

/-! The exact contact polynomial preserves every supported control. The only
input is the finite certificate for the explicit pre-contact high curve. -/
namespace OptimalG.Certificates.StaticCurve
open Set Variational

theorem tail_controls
    (hcontact : ∀ v∈controlFeatureSupport staticLowData,
      (StaticHigh.contactScore:ℝ)≤featureH staticLow_admissible StaticHigh.contact
        StaticHigh.contactValue v) :
    ∀ r∈Icc (StaticHigh.contact:ℝ) 1,∀ v∈controlFeatureSupport staticLowData,
      score r≤featureH staticLow_admissible r (curvePrimitive score r) v := by
  have hs : staticLowData.S∈Icc (0.02271790:ℝ) 0.023354 := by
    norm_num [staticLowData,StaticLow.slack]
  have hq : (StaticHigh.contactRank:ℝ)∈Icc (0.2635:ℝ) 0.28 := by
    norm_num [StaticHigh.contactRank]
  have hb : (StaticHigh.contact:ℝ)∈Ioo zTest 1 := by
    norm_num [StaticHigh.contact,zTest]
  have hline : (StaticHigh.contactScore:ℝ)≤(StaticLow.lam:ℝ)-StaticHigh.contact := by
    norm_num [StaticHigh.contactScore,StaticLow.lam,StaticHigh.contact]
  have hY : (StaticHigh.contactValue:ℝ)≤
      Variational.quadratic StaticLow.lam StaticHigh.contact-staticLowData.S := by
    norm_num [Variational.quadratic,StaticHigh.contactValue,StaticLow.lam,
      StaticHigh.contact,staticLowData,StaticLow.slack]
  have hc : (1-(StaticHigh.contact:ℝ))^2=
      2*((StaticLow.lam:ℝ)-StaticHigh.contactRank)*
        capSlack StaticLow.lam staticLowData.S StaticHigh.contactRank-
        2*capDeficit StaticLow.lam staticLowData.S StaticHigh.contactRank := by
    simpa only [stationaryLevel,staticLowData] using StaticContact.contact_stationary.symm
  have ht := staticLow_admissible.terminal_tail_controls hs hq hb hline hY hcontact hc
    StaticContact.contact_value StaticContact.contact_score
  intro r hr v hv
  have he := tail_values hr
  have hj : curvePrimitive score r=tailPrimitive StaticHigh.contact StaticHigh.contactValue
      StaticHigh.contactScore r := he.2
  rw [he.1,hj]
  exact ht r hr v hv

theorem all_controls
    (hprefix : ∀ r∈Icc zStart (StaticHigh.contact:ℝ),
      ∀ v∈controlFeatureSupport staticLowData,
      score r≤featureH staticLow_admissible r (curvePrimitive score r) v) :
    ∀ r∈Icc zStart 1,∀ v∈controlFeatureSupport staticLowData,
      score r≤featureH staticLow_admissible r (curvePrimitive score r) v := by
  have hcontact : ∀ v∈controlFeatureSupport staticLowData,
      (StaticHigh.contactScore:ℝ)≤featureH staticLow_admissible StaticHigh.contact
        StaticHigh.contactValue v := by
    intro v hv
    have hh := hprefix StaticHigh.contact
      ⟨by norm_num [zStart,StaticHigh.contact],le_rfl⟩ v hv
    have hj : curvePrimitive score StaticHigh.contact=(StaticHigh.contactValue:ℝ) := contact_values.2
    rw [contact_values.1,hj] at hh
    exact hh
  intro r hr v hv
  by_cases hrc : r≤StaticHigh.contact
  · exact hprefix r ⟨hr.1,hrc⟩ v hv
  · exact tail_controls hcontact r ⟨(lt_of_not_ge hrc).le,hr.2⟩ v hv

end OptimalG.Certificates.StaticCurve
