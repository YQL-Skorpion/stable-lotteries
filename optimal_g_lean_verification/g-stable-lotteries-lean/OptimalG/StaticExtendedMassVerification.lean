import OptimalG.IntermediateMixedCoverage
import OptimalG.CapHeadSlopeOrder
import OptimalG.ExtendedMassCoefficients
import OptimalG.ExtendedLocalHigh
import OptimalG.ExtendedLocalTail
import OptimalG.TailSelectedDeficit
import OptimalG.Certificates.StaticExtendedSelectedChecks
import OptimalG.Certificates.StaticExtendedTailChecks

/-! Complete C.4 verification above the last stored support mass.
The finite polynomial certificates supply every scalar sign; the hypotheses
are actual completed-curve geometry and the already established .36 support.
The base high test is used only through .875, and tail propagation is separate. -/
namespace OptimalG
open Set Variational Certificates.ExtendedScalarExpressions
open Certificates.ExtendedCoefficientChecks

namespace VerifierCurve
variable {phi : ℝ → ℝ} (h : VerifierCurve phi (Certificates.StaticLow.lam:ℝ))
include h

theorem static_extended_mass_verified {c p t beta0 eta0 Y H : ℝ}
    (g : BinaryCurveGeometry phi (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) (Certificates.SmallMassExpressions.slope (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ)) c)
    (hS : (Certificates.StaticLow.slack:ℝ) ∈ Icc (227179/10000000 : ℝ) (11677/500000))
    (hp : p ∈ Icc (9/25 : ℝ) (Certificates.StaticLow.lam:ℝ))
    (ht : t ∈ Icc (1529/5000 : ℝ) (9/25))
    (hinitial : phi 0 = Certificates.SmallMassExpressions.initial (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ))
    (hline : ∀ r ∈ Icc (9/25 : ℝ) (391/500), phi r = (Certificates.StaticLow.lam:ℝ)-r)

    (hfirst : beta0*(quadratic (Certificates.StaticLow.lam:ℝ) (1-9/25)-(Certificates.StaticLow.slack:ℝ))+eta0*((Certificates.StaticLow.lam:ℝ)-t)=2*(Certificates.StaticLow.lam:ℝ)-t)
    (hsecond : beta0*(quadratic (Certificates.StaticLow.lam:ℝ) (9/25)-(Certificates.StaticLow.slack:ℝ))-eta0*((Certificates.StaticLow.lam:ℝ)-9/25)=2*(9/25)-(Certificates.StaticLow.lam:ℝ))
    (hsupport : ∀ x∈Icc (0:ℝ) (Certificates.StaticLow.lam:ℝ),x+eta0*phi x≤eta0*(Certificates.StaticLow.lam:ℝ)-(eta0-1)*t)
    (hbase : ∀ z∈Icc (391/500:ℝ) (7/8),
      z-(Certificates.StaticLow.lam:ℝ)+beta0*packingK phi (9/25) 0 z+eta0*phi z≤0)
    (hY : 8793/100000≤Y) (hH : H∈Icc (-(3589/10000):ℝ) (-(1757/5000)))
    (hscore : ∀ z∈Icc (7/8:ℝ) 1,phi z=tailScore (539/625) Y H z)
    (hprimitive : ∀ z∈Icc (7/8:ℝ) 1,curvePrimitive phi z=tailPrimitive (539/625) Y H z)
    (hv : (309/50:ℝ)≤tailBackwardSlope (539/625) Y H)
    (hk : tailBackwardCurvature (539/625) Y H∈Icc (0:ℝ) (1273/100)) :
    ThreeFunctionTest phi (Certificates.StaticLow.lam:ℝ) p
      (extendedBeta (Certificates.StaticLow.lam:ℝ) p t (curvePrimitive phi p) (curvePrimitive phi (1-p)))
      (extendedEta (Certificates.StaticLow.lam:ℝ) p t (curvePrimitive phi p) (curvePrimitive phi (1-p))) := by
  have hL : (Certificates.StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000) := by
    constructor <;> linarith only [g.lambda_mem.1,g.lambda_mem.2]
  have hcapOrder := capHeadSlopeOrder hL hS
  have hfall := g.fall_through_line (top:=391/500)
    (fun r hr => hline r ⟨by linarith only [hr.1,hL.1],hr.2⟩)
  have hp0 : (9/25:ℝ)∈Icc (9/25:ℝ) (Certificates.StaticLow.lam:ℝ) := ⟨le_rfl,by linarith only [hL.1]⟩
  have hN := extended_scalar_denominator_pos hL hS hp ht
  have hN0 := extended_scalar_denominator_pos hL hS hp0 ht
  have hR := g.line_primitive p ⟨by linarith only [hp.1],by linarith only [hp.2,hL.2]⟩
  have hP := g.line_primitive (1-p) ⟨by linarith only [hp.2,hL.2],by linarith only [hp.1]⟩
  have hR0 := g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩
  have hP0 := g.line_primitive (1-9/25) ⟨by norm_num,by norm_num⟩
  have hb0 := extendedBeta_eq_of_system hN0.ne' hfirst hsecond
  have he0 := extendedEta_eq_of_system hN0.ne' hfirst hsecond
  have hbase' (z : ℝ) (hz : z∈Icc (391/500:ℝ) (7/8)) :
      z-(Certificates.StaticLow.lam:ℝ)+extendedBeta (Certificates.StaticLow.lam:ℝ) (9/25) t (curvePrimitive phi (9/25))
        (curvePrimitive phi (1-9/25))*packingK phi (9/25) 0 z+
      extendedEta (Certificates.StaticLow.lam:ℝ) (9/25) t (curvePrimitive phi (9/25))
        (curvePrimitive phi (1-9/25))*phi z≤0 := by
    rw [hR0,hP0,hb0,he0]
    exact hbase z hz
  have hDpos (r : ℝ) (hr : r∈Icc (9/25:ℝ) (Certificates.StaticLow.lam:ℝ)) : 0<etaNumerator (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) r t := by
    have hn := extended_scalar_denominator_pos hL hS hr ht
    have hg := binaryGap_pos hL hS hr
    have hid : etaNumerator (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) r t=denominator (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) r t+binaryGap (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) r := by
      unfold etaNumerator denominator binaryGap
      ring
    rw [hid]
    exact add_pos hn hg
  have hJ : 0<betaNumerator (Certificates.StaticLow.lam:ℝ) p t := by
    have ht0 : 0≤t := by linarith only [ht.1]
    have hm := mul_le_mul_of_nonneg_left hp.2 ht0
    have hg := mul_pos (by linarith only [hL.1] : 0<(Certificates.StaticLow.lam:ℝ))
      (by linarith only [hL.1,ht.2] : 0<(Certificates.StaticLow.lam:ℝ)-t)
    unfold betaNumerator
    nlinarith only [hm,hg]
  have hs : 0<1+Certificates.SmallMassExpressions.slope (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) := by
    have hh := g.head_slope
    linarith only [hh]
  have hdefect := h.selected_deficit_bound hL.2 hS.1 hY hH.1
    (g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩)
    (hprimitive (7/8) ⟨le_rfl,by norm_num⟩)
  have hselected (z : ℝ) (hz : z∈Icc (391/500:ℝ) (7/8)) :
      ∀ q∈Icc (0:ℝ) p,z+q-(Certificates.StaticLow.lam:ℝ)+
        extendedBeta (Certificates.StaticLow.lam:ℝ) p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*packingK phi p q z+
        extendedEta (Certificates.StaticLow.lam:ℝ) p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*phi z≤0 := by
    by_cases hlocal : p≤19/50
    · exact h.extended_local_selected_high g hS ⟨hp.1,hlocal⟩ ht hz hinitial (hbase' z hz)
        (hdefect z ⟨by linarith only [hz.1],hz.2⟩)
    · have hbaseCore := extended_baseCore_nonpos hR0 hP0 hN0
        (g.line_primitive (z-9/25) ⟨by linarith only [hz.1],by linarith only [hz.2]⟩)
        (hbase' z hz)
      exact selected_high_of_scalar_checks h g ⟨(le_of_not_ge hlocal),hp.2⟩ hz hinitial hcapOrder
        hN hJ (hDpos _ hp0) (hDpos _ hp).le hs hbaseCore
        (hdefect z ⟨by linarith only [hz.1],hz.2⟩)
        (Certificates.StaticExtendedSelectedChecks.all_checks hL hS ⟨le_of_not_ge hlocal,hp.2⟩ ht hJ hs)
  apply h.extended_mass_test_with_checked_coefficients hL hS hp ht hinitial hline
    (fun r hr => g.line_primitive r ⟨by linarith only [hr.1],hr.2⟩)
    hfall hfirst hsecond hsupport
  intro z hz q hq hqp
  by_cases hzSelected : z≤7/8
  · exact hselected z ⟨hz.1,hzSelected⟩ q ⟨hq,hqp⟩
  have hzTail : z∈Icc (7/8:ℝ) 1 := ⟨le_of_not_ge hzSelected,hz.2⟩
  by_cases hlocal : p≤19/50
  · have hboxes := local_control_bounds hL hS ⟨hp.1,hlocal⟩ ht
    have hb : 0≤extendedBeta (Certificates.StaticLow.lam:ℝ) p t (curvePrimitive phi p) (curvePrimitive phi (1-p)) := by
      rw [hR,hP,beta_eq]
      exact (div_pos hJ hN).le
    have he : 0<extendedEta (Certificates.StaticLow.lam:ℝ) p t (curvePrimitive phi p) (curvePrimitive phi (1-p)) := by
      rw [hR,hP,eta_eq]
      exact div_pos (hDpos _ hp) hN
    have htheta : 1/extendedEta (Certificates.StaticLow.lam:ℝ) p t (curvePrimitive phi p) (curvePrimitive phi (1-p))≤81/100 := by
      rw [hR,hP,eta_eq,one_div_div]
      exact hboxes.1.2
    have halpha : extendedBeta (Certificates.StaticLow.lam:ℝ) p t (curvePrimitive phi p) (curvePrimitive phi (1-p))/
        extendedEta (Certificates.StaticLow.lam:ℝ) p t (curvePrimitive phi p) (curvePrimitive phi (1-p))≤3 := by
      rw [hR,hP,beta_eq,eta_eq]
      have hid : (betaNumerator (Certificates.StaticLow.lam:ℝ) p t/denominator (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) p t)/
          (etaNumerator (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) p t/denominator (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) p t)=betaNumerator (Certificates.StaticLow.lam:ℝ) p t/etaNumerator (Certificates.StaticLow.lam:ℝ) (Certificates.StaticLow.slack:ℝ) p t := by
        field_simp [hN.ne',(hDpos _ hp).ne']
      rw [hid]
      exact hboxes.2.2
    have hgap : 1≤extendedBeta (Certificates.StaticLow.lam:ℝ) p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*
        (phi 0-(Certificates.StaticLow.lam:ℝ)+391/500-p) := by
      rw [hR,hP,hinitial]
      apply extended_split_gap_of_polynomial hN
      have hh := (localSplit_pos hL hS ⟨hp.1,hlocal⟩ ht).le
      unfold localSplit at hh
      linarith only [hh]
    have hreanchor := tailBackwardCoefficients_reanchor (Y:=Y) (H:=H)
      (by norm_num : (7/8:ℝ)≠1) (by norm_num : (539/625:ℝ)≠1)
    apply h.local_tail_from_selected_endpoint hL.2 ⟨hp.1,hlocal⟩ hb he htheta halpha
      (Y:=tailPrimitive (539/625) Y H (7/8)) (H:=tailScore (539/625) Y H (7/8))
      (by rw [hreanchor.1]; exact hv) (by rw [hreanchor.2]; exact hk)
      (fun r hr => by rw [tailScore_reanchor (by norm_num) (by norm_num)]; exact hscore r hr)
      (fun r hr => by rw [tailPrimitive_reanchor (by norm_num) (by norm_num)]; exact hprimitive r hr)
      (fun r hr => g.line_primitive r ⟨by linarith only [hr.1],by linarith only [hr.2]⟩)
      (fun u hu => by
        have hh := g.low_slope 0 u le_rfl hu.1 hu.2
        linarith only [hh]) hp.2 hgap
      (by simpa only [add_zero] using hselected (7/8) (by norm_num) 0 ⟨le_rfl,by linarith only [hp.1]⟩)
      z hzTail q ⟨hq,hqp⟩
  · exact extended_tail_high_of_polynomial_signs h g ⟨le_of_not_ge hlocal,hp.2⟩ hzTail
      hinitial hcapOrder hN hJ (hDpos _ hp).le hs hY hH (hscore z hzTail) (hprimitive z hzTail)
      (Certificates.StaticExtendedTailChecks.polynomial_signs_lo hL hS ⟨le_of_not_ge hlocal,hp.2⟩ ht)
      (Certificates.StaticExtendedTailChecks.polynomial_signs_hi hL hS ⟨le_of_not_ge hlocal,hp.2⟩ ht)
      q ⟨hq,hqp⟩

end VerifierCurve
end OptimalG
