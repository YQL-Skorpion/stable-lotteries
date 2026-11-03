import OptimalG.SignedControlField
import OptimalG.VariationalDomain
import OptimalG.Certificates.Control
import OptimalG.BoundedContinuation

/-! The actual pre-envelope three-class rational field has well-defined,
continuous Lipschitz envelopes even when low-rank scores are signed. -/
namespace OptimalG.Variational
open Set MeasureTheory
open scoped NNReal

noncomputable def rawDet (lam : ℝ) (J : ℝ → ℝ) (c : Control) : ℝ :=
  (2*lam-c.2.1)*J c.1-(c.1+c.2.2-lam)*J (1-c.1)
noncomputable def rawAlpha (lam : ℝ) (J phi : ℝ → ℝ) (c : Control) : ℝ :=
  ((c.1+c.2.2-lam)*phi c.2.1+(2*lam-c.2.1)*phi c.2.2)/rawDet lam J c
noncomputable def rawBeta (lam : ℝ) (J phi : ℝ → ℝ) (c : Control) : ℝ :=
  (J c.1*phi c.2.1+J (1-c.1)*phi c.2.2)/rawDet lam J c
noncomputable def rawVectorField (lam : ℝ) (J phi : ℝ → ℝ) (z u : ℝ) : ℝ :=
  signedVectorField lam J (rawAlpha lam J phi) (rawBeta lam J phi) (·.1) controlMeasure z u

theorem control_coordinates_bounded :
    EssentiallyBounded (fun c : Control => c.1) controlMeasure ∧
    EssentiallyBounded (fun c : Control => c.2.1) controlMeasure ∧
    EssentiallyBounded (fun c : Control => c.2.2) controlMeasure := by
  have hm : ∀ᵐ c ∂controlMeasure, c ∈ controlDomain := ae_restrict_mem controlDomain_measurable
  refine ⟨⟨1, ?_⟩, ⟨1, ?_⟩, ⟨1, ?_⟩⟩
  · filter_upwards [hm] with c hc
    have hp := hc.1
    norm_num [pLo,pHi] at hp
    exact abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩
  · filter_upwards [hm] with c hc
    have hx := hc.2.1
    norm_num [xLo,xHi] at hx
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · filter_upwards [hm] with c hc
    have hlo := (le_max_left xLo c.1).trans hc.2.2.1
    have hhi := hc.2.2.2
    norm_num [xLo,xHi] at hlo hhi
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem raw_coefficients_bounded {lam delta : ℝ} {J phi : ℝ → ℝ} {K : ℝ≥0}
    (hJ : LipschitzWith K J) (hd : 0 < delta)
    (hdet : ∀ c ∈ controlDomain, delta ≤ rawDet lam J c)
    (hx : EssentiallyBounded (fun c : Control => phi c.2.1) controlMeasure)
    (hy : EssentiallyBounded (fun c : Control => phi c.2.2) controlMeasure) :
    EssentiallyBounded (rawAlpha lam J phi) controlMeasure ∧
    EssentiallyBounded (rawBeta lam J phi) controlMeasure := by
  obtain ⟨hp,hcx,hcy⟩ := control_coordinates_bounded
  have hk := (hp.add hcy).sub (EssentiallyBounded.const lam)
  have hh := (EssentiallyBounded.const (2*lam)).sub hcx
  have hR := hp.comp_lipschitz hJ
  have hP := ((EssentiallyBounded.const 1).sub hp).comp_lipschitz hJ
  have hD : ∀ᵐ c ∂controlMeasure, delta ≤ |rawDet lam J c| := by
    have hm : ∀ᵐ c ∂controlMeasure, c ∈ controlDomain := ae_restrict_mem controlDomain_measurable
    filter_upwards [hm] with c hc
    exact (hdet c hc).trans (le_abs_self _)
  exact ⟨((hk.mul hx).add (hh.mul hy)).div_of_abs_lower delta hd hD,
    ((hR.mul hx).add (hP.mul hy)).div_of_abs_lower delta hd hD⟩

theorem rawControl_eq_value (lam : ℝ) (J phi : ℝ → ℝ) (z u : ℝ) (c : Control) :
    signedControlH lam J (rawAlpha lam J phi) (rawBeta lam J phi) (·.1) z u c =
      Certificates.Control.value (z-lam) (2*lam-c.2.1) (c.1+c.2.2-lam)
        (J c.1) (J (1-c.1)) (J (z-c.1)-u) (phi c.2.1) (phi c.2.2) := by
  unfold signedControlH rawAlpha rawBeta rawDet Certificates.Control.value
    Certificates.Control.det Certificates.Control.alphaNumerator
  ring

/-- No positivity of phi is used here. Continuous bounded primitive data and
a positive determinant suffice for the signed field before the envelope. -/
theorem rawVectorField_regular {lam delta : ℝ} {J phi : ℝ → ℝ} {K : ℝ≥0}
    (hJ : LipschitzWith K J) (hd : 0 < delta)
    (hdet : ∀ c ∈ controlDomain, delta ≤ rawDet lam J c)
    (hx : EssentiallyBounded (fun c : Control => phi c.2.1) controlMeasure)
    (hy : EssentiallyBounded (fun c : Control => phi c.2.2) controlMeasure) :
    ∃ KA : ℝ≥0, (∀ z, LipschitzWith KA (rawVectorField lam J phi z)) ∧
      ∀ u, Continuous (fun z => rawVectorField lam J phi z u) := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := raw_coefficients_bounded hJ hd hdet hx hy
  let KA : ℝ≥0 := ⟨|a|,abs_nonneg a⟩
  let KB : ℝ≥0 := ⟨|b|,abs_nonneg b⟩
  have hA : ∀ᵐ c ∂controlMeasure, |rawAlpha lam J phi c| ≤ KA := by
    filter_upwards [ha] with c hc
    exact hc.trans (le_abs_self a)
  have hB : ∀ᵐ c ∂controlMeasure, |rawBeta lam J phi c| ≤ KB := by
    filter_upwards [hb] with c hc
    exact hc.trans (le_abs_self b)
  refine ⟨KA, ?_, ?_⟩
  · intro z
    exact signedVectorField_state_lipschitz hJ hA ⟨b,hb⟩ control_coordinates_bounded.1 z
  · intro u
    exact (signedVectorField_time_lipschitz hJ hA hB control_coordinates_bounded.1 u).continuous

end OptimalG.Variational
