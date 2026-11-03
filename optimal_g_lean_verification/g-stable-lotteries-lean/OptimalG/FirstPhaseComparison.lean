import OptimalG.FirstPhaseGeometry
import OptimalG.SignedRationalControl

/-! Finite clipped-control comparison for the concrete first slack-removal phase. -/
namespace OptimalG.Relocation
open Set

 theorem first_control_comparison {lam : ℝ} {phi : ℝ → ℝ}
    (h : NormalizedNecessaryTwoClass lam phi) (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p x y z Y err : ℝ}
    (hp : p ∈ Icc (0.25 : ℝ) 0.36) (hx : x ∈ Icc (0.285 : ℝ) 0.38)
    (hy : y ∈ Icc (0.285 : ℝ) 0.38) (hpy : p ≤ y)
    (hz : z ∈ Icc (0.775 : ℝ) 0.875)
    (hYlo : linePrimitive lam z-linePrimitive lam 1 ≤ Y)
    (hYhi : Y ≤ linePrimitive lam z-slack lam phi 0.775)
    (he : err ∈ Icc (0 : ℝ) (0.784*massOne lam phi)) :
    min (lam-z) (Certificates.Control.value (z-lam) (2*lam-x) (p+y-lam)
      (activationPrimitive phi p) (activationPrimitive phi (1-p))
      (activationPrimitive phi (z-p)-Y) (phi x) (phi y)) -
        (6.19*massOne lam phi+4.53*err) ≤
    min (lam-z) (Certificates.Control.value (z-lam) (2*lam-x) (p+y-lam)
      (firstPrimitive lam phi p) (firstPrimitive lam phi (1-p))
      (firstPrimitive lam phi (z-p)-(Y+prefixGain lam phi+massOne lam phi-err)) (phi x) (phi y)) := by
  have hm := (mass_budget h hL hLP).1
  have heta : 0 ≤ prefixGain lam phi := mul_nonneg (by norm_num) hm
  have hdk := (first_gain_bounds h hL hLP (r := z-p) (by linarith [hz.1,hp.2])).2
  have hdk' : firstMiddleGain lam phi (z-p) ≤ massOne lam phi := by
    unfold firstMiddleGain
    linarith
  have hU : z-lam ∈ Icc (0.21267 : ℝ) 0.313 :=
    ⟨by linarith [hz.1,hL.2],by linarith [hz.2,hL.1]⟩
  have hh := Certificates.Control.phaseValue_clipped_of_geometry hL hp hx hy hpy hU
    (h.ceiling x ⟨by linarith [hx.1],by linarith [hx.2]⟩)
    (h.ceiling y ⟨by linarith [hy.1],by linarith [hy.2]⟩)
    heta hm he.1 (dp := massOne lam phi) le_rfl hdk'
    (fun t ht => first_phase_geometry h hL hLP hp hx hy hz ht hYlo hYhi he)
  have hRP := first_RP_increments h hL hLP hp
  have hr : z-p ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hz.1,hp.2],by linarith [hz.2,hp.1]⟩
  have hK : activationPrimitive phi (z-p)-Y+firstMiddleGain lam phi (z-p)-massOne lam phi+err =
      firstPrimitive lam phi (z-p)-(Y+prefixGain lam phi+massOne lam phi-err) := by
    unfold firstMiddleGain firstPrimitive
    rw [slack_eq lam phi hr]
    unfold cumulativeSlack
    ring
  rw [hK,show -(z-lam)=lam-z by ring] at hh
  rw [hRP.1,hRP.2]
  exact hh

/-- The same comparison uses the globally Lipschitz primitive extensions
that enter the actual signed ODE. -/
theorem first_raw_control_comparison {lam : ℝ} {phi : ℝ → ℝ}
    (h : NormalizedNecessaryTwoClass lam phi) (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {c : Variational.Control} {z Y err : ℝ}
    (hc : c ∈ Variational.controlDomain) (hz : z ∈ Icc (0.775 : ℝ) 0.875)
    (hYlo : linePrimitive lam z-linePrimitive lam 1 ≤ Y)
    (hYhi : Y ≤ linePrimitive lam z-slack lam phi 0.775)
    (he : err ∈ Icc (0 : ℝ) (0.784*massOne lam phi)) :
    min (lam-z) (Variational.signedControlH lam (extendedPrimitive phi)
      (Variational.rawAlpha lam (extendedPrimitive phi) phi)
      (Variational.rawBeta lam (extendedPrimitive phi) phi) (·.1) z Y c) -
        (6.19*massOne lam phi+4.53*err) ≤
    min (lam-z) (Variational.signedControlH lam (firstExtendedPrimitive lam phi)
      (Variational.rawAlpha lam (firstExtendedPrimitive lam phi) phi)
      (Variational.rawBeta lam (firstExtendedPrimitive lam phi) phi) (·.1) z
      (Y+prefixGain lam phi+massOne lam phi-err) c) := by
  have hp : c.1 ∈ Icc (0.25 : ℝ) 0.36 := by
    convert hc.1 using 1 <;> norm_num [Variational.pLo,Variational.pHi]
  have hx : c.2.1 ∈ Icc (0.285 : ℝ) 0.38 := by
    convert hc.2.1 using 1 <;> norm_num [Variational.xLo,Variational.xHi]
  have hyl := (le_max_left Variational.xLo c.1).trans hc.2.2.1
  have hy : c.2.2 ∈ Icc (0.285 : ℝ) 0.38 := by
    convert (show c.2.2 ∈ Icc Variational.xLo Variational.xHi from ⟨hyl,hc.2.2.2⟩) using 1 <;>
      norm_num [Variational.xLo,Variational.xHi]
  have hpy := (le_max_right Variational.xLo c.1).trans hc.2.2.1
  have hpI : c.1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hp.1],by linarith [hp.2]⟩
  have hpcI : 1-c.1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hp.2],by linarith [hp.1]⟩
  have hrI : z-c.1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hz.1,hp.2],by linarith [hz.2,hp.1]⟩
  rw [Variational.rawControl_eq_value,Variational.rawControl_eq_value,
    extendedPrimitive_eq phi hpI,extendedPrimitive_eq phi hpcI,extendedPrimitive_eq phi hrI,
    firstExtended_eq lam phi hpI,firstExtended_eq lam phi hpcI,firstExtended_eq lam phi hrI]
  exact first_control_comparison h hL hLP hp hx hy hpy hz hYlo hYhi he

end OptimalG.Relocation
