import OptimalG.ExtendedSelectedAnalytic
import OptimalG.ExtendedHighReduction

/-! Coverage of every selected-high split from explicit scalar endpoint
checks. The unknown score and integral primitive occur only in genuine
curve-geometry hypotheses and in the established base control. -/
namespace OptimalG
open Set Variational Certificates.ExtendedScalarExpressions
open Certificates.ExtendedLocalExpressions Certificates.ExtendedSelectedExpressions

/-- These are explicit rational/positive-part expressions on compact scalar
boxes. No field is an inequality involving an unknown score or primitive. -/
structure ExtendedSelectedChecks (lam S p t : ℝ) : Prop where
  head_start : ∀ e∈Icc (0:ℝ) (17/5000),headGain lam S p t (391/500) e≤0
  head_finish : ∀ e∈Icc (0:ℝ) (17/5000),headGain lam S p t (7/8) e≤0
  high_rank : ∀ z∈Icc (391/500:ℝ) (7/8),∀ e∈Icc (0:ℝ) (17/5000),
    highRankCore lam S p t z e (527/2000)≤0 ∧ highRankCore lam S p t z e p≤0
  cap_endpoints : ∀ z∈Icc (391/500:ℝ) (7/8),∀ e∈Icc (0:ℝ) (17/5000),z-p≤9/25→
    capCore lam S p t z e 0≤0 ∧ capCore lam S p t z e (9/25-z+p)≤0

 theorem selected_high_of_scalar_checks {phi : ℝ→ℝ} {lam S c p t z : ℝ}
    (h : VerifierCurve phi lam)
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
    (hp : p∈Icc (19/50:ℝ) lam) (hz : z∈Icc (391/500:ℝ) (7/8))
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial lam S)
    (hcapOrder : ∀ u∈Icc (0:ℝ) (9/25),∀ v∈Icc (0:ℝ) (9/25),u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤capScore lam S v-capScore lam S u)
    (hN : 0<denominator lam S p t) (hJ : 0<betaNumerator lam p t)
    (hD0 : 0<etaNumerator lam S (9/25) t) (hD : 0≤etaNumerator lam S p t)
    (hs : 0<1+Certificates.SmallMassExpressions.slope lam S)
    (hbase : extendedBaseCore lam S (9/25) t z (primitiveDefect phi lam S z) (phi z)≤0)
    (hdefect : primitiveDefect phi lam S z∈Icc (0:ℝ) (17/5000))
    (checks : ExtendedSelectedChecks lam S p t) :
    ∀ q∈Icc (0:ℝ) p,z+q-lam+
      extendedBeta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*packingK phi p q z+
      extendedEta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*phi z≤0 := by
  have hR := g.line_primitive p ⟨by linarith only [hp.1],by linarith only [hp.2,g.lambda_mem.2]⟩
  have hP := g.line_primitive (1-p) ⟨by linarith only [hp.2,g.lambda_mem.2],by linarith only [hp.1]⟩
  have hline := h.primitive_le_quadratic_after_anchor (a:=9/25)
    (by norm_num) (g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩)
  intro q hq
  have hr : z-p+q∈Icc (0:ℝ) 1 :=
    ⟨by linarith only [hz.1,hp.2,g.lambda_mem.2,hq.1],by linarith only [hz.2,hq.2]⟩
  by_cases hqh : 527/2000≤q
  · have hslack : quadratic lam q-curvePrimitive phi q≤S := by
      have hh := h.binarySlackArea_antitone S
        ⟨hq.1,by linarith only [hq.2,hp.2,g.lambda_mem.2]⟩
        (b:=31/40) (by norm_num)
        (by linarith only [hq.2,hp.2,g.lambda_mem.2])
      unfold binarySlackArea at hh
      rw [g.line_primitive (31/40) ⟨by norm_num,le_rfl⟩] at hh
      linarith only [hh]
    have hremaining := hline (z-p+q) ⟨by linarith only [hz.1,hp.2,g.lambda_mem.2,hqh],hr.2⟩
    apply extended_high_of_core hR hP hN hJ.le hslack
      (show curvePrimitive phi (z-p+q)-quadratic lam (z-p+q)+S≤0 by linarith only [hremaining])
    apply extended_compare_nonpos hD0 hD hbase
    rw [←highRankCore_identity]
    have hh := checks.high_rank z hz _ hdefect
    exact extended_highRankCore_le_endpoints hh.1 hh.2 q ⟨hqh,hq.2⟩
  · have hhead : curvePrimitive phi q=Certificates.SmallMassExpressions.primitive lam S q := by
      rw [h.affine_head_primitive g.head ⟨hq.1,le_of_not_ge hqh⟩,hinitial]
      rfl
    have hslack : quadratic lam q-curvePrimitive phi q≤
        quadratic lam q-Certificates.SmallMassExpressions.primitive lam S q := by rw [hhead]
    by_cases hrl : 9/25≤z-p+q
    · have hremaining := hline (z-p+q) ⟨hrl,hr.2⟩
      apply extended_high_of_core hR hP hN hJ.le hslack
        (show curvePrimitive phi (z-p+q)-quadratic lam (z-p+q)+S≤0 by linarith only [hremaining])
      apply extended_compare_nonpos hD0 hD hbase
      rw [←headCore_identity]
      exact (extended_headCore_le_gain hD0.le hJ hs hq.1).trans
        (extended_headGain_le_endpoints hD0.le hJ hs (checks.head_start _ hdefect)
          (checks.head_finish _ hdefect) z hz)
    · have hshift := g.cap_upper (z-p+q) ⟨hr.1,by linarith only [hrl]⟩
      apply extended_high_of_core hR hP hN hJ.le hslack
        (show curvePrimitive phi (z-p+q)-quadratic lam (z-p+q)+S≤
          cap lam S (z-p+q)-quadratic lam (z-p+q)+S by linarith only [hshift])
      apply extended_compare_nonpos hD0 hD hbase
      rw [←capCore_identity]
      have harg : z-p≤9/25 := by linarith only [hrl,hq.1]
      have hh := checks.cap_endpoints z hz _ hdefect harg
      apply extended_capCore_le_endpoints hD0.le hJ.le
        (by linarith only [harg] : (0:ℝ)≤9/25-z+p) (by linarith : z-p+(9/25-z+p)<1) _ hh.1 hh.2
        q ⟨hq.1,by linarith only [hrl]⟩
      intro u hu v hv huv
      have hu' : z-p+u∈Icc (0:ℝ) (9/25) :=
        ⟨by linarith only [hz.1,hp.2,g.lambda_mem.2,hu.1],by linarith only [hu.2]⟩
      have hv' : z-p+v∈Icc (0:ℝ) (9/25) :=
        ⟨by linarith only [hz.1,hp.2,g.lambda_mem.2,hv.1],by linarith only [hv.2]⟩
      have hh := hcapOrder _ hu' _ hv' (by linarith only [huv])
      convert! hh using 1 <;> ring

end OptimalG
