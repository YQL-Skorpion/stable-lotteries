import OptimalG.Certificates.StaticLowBounds

/-! The static low curve satisfies the genuine variational low constraints.
The sufficient election certificate will use its explicit score as well. -/
namespace OptimalG.Variational
open Set MeasureTheory

noncomputable def staticLowData : LowRankData :=
  ⟨Certificates.StaticLow.slack,Certificates.StaticLow.score⟩

theorem lowPrimitive_staticLow (r : ℝ) :
    lowPrimitive Certificates.StaticLow.lam staticLowData r=
      Certificates.StaticLow.primitive r := by
  have hh := Certificates.StaticLow.primitive_integral r
  change cap Certificates.StaticLow.lam Certificates.StaticLow.slack ell+
    (∫ t in ell..r,Certificates.StaticLow.score t)=_
  norm_num [ell,cap,Certificates.cap] at hh ⊢
  exact hh

theorem staticLow_admissible : Admissible Certificates.StaticLow.lam staticLowData := by
  have hb : ∀ᵐ r ∂volume.restrict (Icc ell tEnd),
      0≤Certificates.StaticLow.score r ∧
      Certificates.StaticLow.score r≤(Certificates.StaticLow.lam:ℝ)-r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    apply Certificates.StaticLow.score_bounds
    norm_num [ell,tEnd] at hr ⊢
    exact hr
  have hnorm : ∀ᵐ r ∂volume.restrict (Icc ell tEnd),
      ‖Certificates.StaticLow.score r‖≤1 := by
    filter_upwards [hb,ae_restrict_mem measurableSet_Icc] with r hs hr
    rw [Real.norm_eq_abs,abs_of_nonneg hs.1]
    have hlo := hr.1
    norm_num [ell] at hlo
    have hhi := hs.2
    norm_num [Certificates.StaticLow.lam] at hhi
    linarith only [hlo,hhi]
  refine ⟨?_,?_,?_,hb,?_,?_⟩
  · norm_num [lambdaLo,lambdaHi,Certificates.StaticLow.lam]
  · norm_num [staticLowData,slackUpper,lambdaHi,Certificates.StaticLow.lam,
      Certificates.StaticLow.slack]
  · exact memLp_top_of_bound Certificates.StaticLow.continuous_score.aestronglyMeasurable 1 hnorm
  · rw [lowPrimitive_staticLow]
    have hh := Certificates.StaticLow.primitive_line (r:=(0.385:ℝ))
      (by linarith only [Certificates.StaticLow.contacts_real.2.2.2])
    convert! hh using 1 <;>
      norm_num [tEnd,quadratic,Certificates.quadratic,staticLowData]
  · intro r hr
    rw [lowPrimitive_staticLow]
    exact Certificates.StaticLow.primitive_le_cap (by have hh := hr.2; norm_num [tEnd] at hh ⊢; exact hh)

end OptimalG.Variational
