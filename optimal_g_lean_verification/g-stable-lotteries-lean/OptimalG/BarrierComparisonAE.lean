import OptimalG.BarrierComparison
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Convex.Continuous

/-! The high score can change active controls without possessing an ordinary
second derivative at the switch. Absolute continuity of the first derivatives
and an almost-everywhere curvature comparison suffice. -/
namespace OptimalG
open Set MeasureTheory

/-- Concavity supplies the required absolute continuity on every compact
interval strictly inside its shape domain. No second derivative is assumed. -/
theorem concave_absolutelyContinuousOnInterval {f : ℝ → ℝ} {c d a b : ℝ}
    (hc : ConcaveOn ℝ (Icc c d) f) (hab : a≤b) (hca : c<a) (hbd : b<d) :
    AbsolutelyContinuousOnInterval f a b := by
  have hsub : Icc a b ⊆ interior (Icc c d) := by
    rw [interior_Icc]
    intro r hr
    exact ⟨hca.trans_le hr.1,hr.2.trans_lt hbd⟩
  obtain ⟨K,hK⟩ := (hc.locallyLipschitzOn_interior.mono hsub).exists_lipschitzOnWith_of_compact
    isCompact_Icc
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le hab] using hK

/-- Fundamental-theorem comparison on every subinterval of an absolutely
continuous pair, from an AE comparison of their actual derivatives. -/
theorem ac_increment_comparison {f g : ℝ → ℝ} {a b x y : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hd : ∀ᵐ r ∂volume.restrict (Icc a b),deriv f r≤deriv g r)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x≤y) :
    f y-f x≤g y-g x := by
  have hab : a≤b := hx.1.trans hx.2
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hsub' : uIcc x y ⊆ uIcc a b := by
    rw [uIcc_of_le hxy,uIcc_of_le hab]
    exact hsub
  have hf' := hf.mono hsub'
  have hg' := hg.mono hsub'
  have hh := intervalIntegral.integral_mono_ae_restrict hxy hf'.intervalIntegrable_deriv
    hg'.intervalIntegrable_deriv (ae_restrict_of_ae_restrict_of_subset hsub hd)
  rw [hf'.integral_deriv_eq_sub,hg'.integral_deriv_eq_sub] at hh
  exact hh

/-- The comparison needed for the actual concave high score: first derivatives
are AC, second derivatives are compared only almost everywhere. -/
theorem barrier_comparison_of_ac_slopes {a b : ℝ} {Y T dY dT : ℝ → ℝ}
    (hY : ContinuousOn Y (Icc a b)) (hT : ContinuousOn T (Icc a b))
    (hdY : AbsolutelyContinuousOnInterval dY a b)
    (hdT : AbsolutelyContinuousOnInterval dT a b)
    (hYd : ∀ r ∈ Ioo a b,HasDerivAt Y (dY r) r)
    (hTd : ∀ r ∈ Ioo a b,HasDerivAt T (dT r) r)
    (hcurvature : ∀ᵐ r ∂volume.restrict (Icc a b),deriv dT r≤deriv dY r)
    (hvalue : T a≤Y a) (hslope : dT a≤dY a) :
    ∀ r ∈ Icc a b,T r≤Y r := by
  have hslopeAll : ∀ r ∈ Icc a b,dT r≤dY r := by
    intro r hr
    have hh := ac_increment_comparison hdT hdY hcurvature
      (show a ∈ Icc a b from ⟨le_rfl,hr.1.trans hr.2⟩) hr hr.1
    linarith
  have hmono : MonotoneOn (fun r => Y r-T r) (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) (hY.sub hT)
      (f':=fun r => dY r-dT r)
    · intro r hr
      have hr' : r ∈ Ioo a b := by simpa using hr
      convert! ((hYd r hr').sub (hTd r hr')).hasDerivWithinAt using 1
    · intro r hr
      exact sub_nonneg.mpr (hslopeAll r (interior_subset hr))
  intro r hr
  have hh := hmono ⟨le_rfl,hr.1.trans hr.2⟩ hr hr.1
  dsimp only at hh
  linarith

/-- A fully AE version is available when the primitive curves themselves are
presented as absolutely continuous functions. -/
theorem barrier_comparison_of_ae_second_derivatives {a b : ℝ} {Y T dY dT : ℝ → ℝ}
    (hY : AbsolutelyContinuousOnInterval Y a b)
    (hT : AbsolutelyContinuousOnInterval T a b)
    (hdY : AbsolutelyContinuousOnInterval dY a b)
    (hdT : AbsolutelyContinuousOnInterval dT a b)
    (hYd : ∀ᵐ r ∂volume.restrict (Icc a b),HasDerivAt Y (dY r) r)
    (hTd : ∀ᵐ r ∂volume.restrict (Icc a b),HasDerivAt T (dT r) r)
    (hcurvature : ∀ᵐ r ∂volume.restrict (Icc a b),deriv dT r≤deriv dY r)
    (hvalue : T a≤Y a) (hslope : dT a≤dY a) :
    ∀ r ∈ Icc a b,T r≤Y r := by
  have hslopeAll : ∀ r ∈ Icc a b,dT r≤dY r := by
    intro r hr
    have hh := ac_increment_comparison hdT hdY hcurvature
      (show a ∈ Icc a b from ⟨le_rfl,hr.1.trans hr.2⟩) hr hr.1
    linarith
  have hfirst : ∀ᵐ r ∂volume.restrict (Icc a b),deriv T r≤deriv Y r := by
    filter_upwards [hYd,hTd,ae_restrict_mem measurableSet_Icc] with r hYr hTr hr
    rw [hYr.deriv,hTr.deriv]
    exact hslopeAll r hr
  intro r hr
  have hh := ac_increment_comparison hT hY hfirst
    (show a ∈ Icc a b from ⟨le_rfl,hr.1.trans hr.2⟩) hr hr.1
  linarith

end OptimalG
