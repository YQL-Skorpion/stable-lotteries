import OptimalG.ExtendedHighReduction
import OptimalG.Certificates.ExtendedCoefficientChecks
import OptimalG.Certificates.ExtendedLocalChecks

/-! The local extended masses .36 through .38 inherit the base selected-high
control from exact checked transport polynomials. The low-rank split is
eliminated by a checked derivative-gap inequality. -/
namespace OptimalG
open Set Variational Certificates.ExtendedScalarExpressions
open Certificates.ExtendedCoefficientChecks Certificates.ExtendedLocalChecks

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem extended_local_selected_high {S slope c p t z : ℝ}
    (g : BinaryCurveGeometry phi lam S slope c)
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (9/25:ℝ) (19/50))
    (ht : t∈Icc (1529/5000:ℝ) (9/25))
    (hz : z∈Icc (391/500:ℝ) (7/8))
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial lam S)
    (hbase : z-lam+extendedBeta lam (9/25) t (curvePrimitive phi (9/25))
        (curvePrimitive phi (1-9/25))*packingK phi (9/25) 0 z+
      extendedEta lam (9/25) t (curvePrimitive phi (9/25))
        (curvePrimitive phi (1-9/25))*phi z≤0)
    (hdefect : primitiveDefect phi lam S z∈Icc (0:ℝ) (17/5000)) :
    ∀ q∈Icc (0:ℝ) p,
      z+q-lam+extendedBeta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*
        packingK phi p q z+
        extendedEta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*phi z≤0 := by
  have hL : lam∈Icc (22493/40000:ℝ) (56233/100000) :=
    ⟨by linarith only [g.lambda_mem.1],by linarith only [g.lambda_mem.2]⟩
  have hpL : p∈Icc (9/25:ℝ) lam := ⟨hp.1,by linarith only [hp.2,hL.1]⟩
  have hp0 : (9/25:ℝ)∈Icc (9/25:ℝ) lam := ⟨le_rfl,by linarith only [hL.1]⟩
  have hN := extended_scalar_denominator_pos hL hS hpL ht
  have hN0 := extended_scalar_denominator_pos hL hS hp0 ht
  have hD : 0<etaNumerator lam S p t := by
    have hh := binaryGap_pos hL hS hpL
    have he : etaNumerator lam S p t=denominator lam S p t+binaryGap lam S p := by
      unfold etaNumerator denominator binaryGap
      ring
    rw [he]
    positivity
  have hD0 : 0<etaNumerator lam S (9/25) t := by
    have hh := binaryGap_pos hL hS hp0
    have he : etaNumerator lam S (9/25) t=denominator lam S (9/25) t+binaryGap lam S (9/25) := by
      unfold etaNumerator denominator binaryGap
      ring
    rw [he]
    positivity
  have hJ : 0<betaNumerator lam p t := by
    have hm := mul_le_mul ht.2 hp.2 (by linarith only [hp.1]) (by norm_num : (0:ℝ)≤9/25)
    unfold betaNumerator
    nlinarith only [hm,hL.1]
  have hR := g.line_primitive p ⟨by linarith only [hp.1],by linarith only [hp.2]⟩
  have hP := g.line_primitive (1-p) ⟨by linarith only [hp.2],by linarith only [hp.1]⟩
  have hR0 := g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩
  have hP0 := g.line_primitive (1-9/25) ⟨by norm_num,by norm_num⟩
  have hbaseCore := extended_baseCore_nonpos hR0 hP0 hN0
    (g.line_primitive (z-9/25) ⟨by linarith only [hz.1],by linarith only [hz.2]⟩) hbase
  have hcore : extendedHighCore lam S p t 0 z (primitiveDefect phi lam S z) 0 0 (phi z)≤0 := by
    apply extended_compare_nonpos hD0 hD.le hbaseCore
    rw [Certificates.ExtendedLocalExpressions.zero_split_identity]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hp.1)
      (localCore_neg hL hS ⟨hp.1,by linarith only [hp.2]⟩ hz ht hdefect).le
  have hzero := extended_high_of_core hR hP hN hJ.le
    (su:=0) (eu:=0) (by simp [quadratic,curvePrimitive]) (by
      rw [add_zero,g.line_primitive (z-p)
        ⟨by linarith only [hz.1,hp.2],by linarith only [hz.2,hp.1]⟩]
      linarith) hcore
  have hbeta : 0≤extendedBeta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p)) := by
    rw [hR,hP,beta_eq]
    exact (div_pos hJ hN).le
  have hgap : 1≤extendedBeta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*
      (phi 0-lam+391/500-p) := by
    rw [hR,hP,hinitial]
    apply extended_split_gap_of_polynomial hN
    have hh := (localSplit_pos hL hS hp ht).le
    unfold localSplit at hh
    linarith only [hh]
  intro q hq
  have hg : 1≤extendedBeta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*
      (phi 0-lam+z-p) :=
    hgap.trans (mul_le_mul_of_nonneg_left (by linarith only [hz.1]) hbeta)
  have hh := h.testValue_le_zero_split (fun u hu => by
    have hh := g.low_slope 0 u le_rfl hu.1 hu.2
    linarith only [hh]) hq.1 hq.2 (hq.2.trans hpL.2)
    (by linarith only [hp.2,hz.1]) (by linarith only [hz.2]) hbeta hg
  simpa only [add_zero] using (show z+q-lam+extendedBeta lam p t (curvePrimitive phi p)
      (curvePrimitive phi (1-p))*packingK phi p q z+
      extendedEta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*phi z≤0 by
    linarith only [hzero,hh])

end VerifierCurve
end OptimalG
